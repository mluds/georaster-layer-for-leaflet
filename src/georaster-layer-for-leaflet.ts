/* global proj4 */
import "regenerator-runtime/runtime.js";
import * as L from "leaflet";
import chroma from "chroma-js";
import geocanvas from "geocanvas";
import { rawToRgb } from "pixel-utils";
import isUTM from "utm-utils/src/isUTM.js";
import getProjString from "utm-utils/src/getProjString.js";
import type { Coords, DoneCallback, LatLngBounds, LatLngTuple } from "leaflet";
import proj4FullyLoaded from "proj4-fully-loaded";
import { GeoExtent } from "geo-extent";
import snap from "snap-bbox";
import Dexie, { Table } from "dexie";
import { v4 as uuidv4 } from "uuid";

import type {
  CustomCRS,
  CustomCSSStyleDeclaration,
  GeoRasterLayerOptions,
  GeoRaster,
  GeoRasterKeys,
  GetRasterOptions,
  DrawTileOptions,
  Mask,
  MaskStrategy,
  PixelValuesToColorFn,
  Tile
} from "./types";

const EPSG4326 = 4326;
const PROJ4_SUPPORTED_PROJECTIONS = new Set([3785, 3857, 4269, 4326, 900913, 102113]);
const MAX_NORTHING = 1000;
const MAX_EASTING = 1000;
const ORIGIN: LatLngTuple = [0, 0];
const RGB_MIN = 0;
const RGB_MAX = 255;
const YCBCR_INTERP = 6;

const log = (obj: any) => console.log("[georaster-layer-for-leaflet] ", obj);

interface CachedTile {
  id?: number;
  key: string;
  tile: string;
}

class Database extends Dexie {
  cachedTiles!: Table<CachedTile>;

  constructor() {
    super("georaster-layer-for-leaflet-cache");
    this.version(1).stores({
      cachedTiles: "++id, key"
    });
  }
}

const db = new Database();

// figure out if simple CRS
// even if not created with same instance of LeafletJS
const isSimpleCRS = (crs: CustomCRS) =>
  crs === L.CRS.Simple ||
  (!crs.code &&
    crs.infinite &&
    crs?.transformation?._a === 1 &&
    crs?.transformation?._b === 0 &&
    crs?.transformation?._c === -1 &&
    crs?.transformation?._d === 0);

if (!L)
  console.warn(
    "[georaster-layer-for-leaflet] can't find Leaflet.  If you are loading via <script>, please add the GeoRasterLayer script after the LeafletJS script."
  );

const zip = (a: any[], b: any[]) => a.map((it, i) => [it, b[i]]);

const GeoRasterLayer: (new (options: GeoRasterLayerOptions) => any) & typeof L.Class = L.GridLayer.extend({
  options: {
    updateWhenIdle: true,
    updateWhenZooming: false,
    keepBuffer: 25,
    resolution: 2 ** 5,
    debugLevel: 0,
    caching: true,
    minValues: [0],
    maxValues: [255]
  },

  cache: {},

  initialize: function (options: GeoRasterLayerOptions) {

    this.rasterIndex = options.rasterIndex;
    this.minValues = options.minValues ?? this.options.minValues;
    this.maxValues = options.maxValues ?? this.options.maxValues;

    try {
      if (options.georasters) {
        this.georasters = options.georasters;
      } else if (options.georaster) {
        this.georasters = [options.georaster];
      } else {
        throw new Error("You initialized a GeoRasterLayer without a georaster or georasters value.");
      }

      if (this.sourceType === "url") {
        options.updateWhenIdle = false;
        options.updateWhenZooming = true;
        options.keepBuffer = 16;
      }

      if (options.resampleMethod) {
        this.resampleMethod = options.resampleMethod;
      }

      /*
          Unpacking values for use later.
          We do this in order to increase speed.
      */
      const keys = [
        "height",
        "width",
        "noDataValue",
        "palette",
        "pixelHeight",
        "pixelWidth",
        "projection",
        "sourceType",
        "xmin",
        "xmax",
        "ymin",
        "ymax"
      ];
      if (this.georasters.length > 1) {
        keys.forEach(key => {
          if (this.same(this.georasters, key)) {
            this[key] = this.georasters[0][key];
          } else {
            throw new Error("all GeoRasters must have the same " + key);
          }
        });
      } else if (this.georasters.length === 1) {
        keys.forEach(key => {
          this[key] = this.georasters[0][key];
        });
      }

      if (options.noDataValue) this.noDataValue = options.noDataValue;

      this._cache = {
        innerTile: {},
        tile: {}
      };

      this.extent = new GeoExtent([this.xmin, this.ymin, this.xmax, this.ymax], { srs: this.projection });

      // used later if simple projection
      this.ratio = this.height / this.width;

      this.debugLevel = options.debugLevel;
      if (this.debugLevel >= 1) log({ options });

      if (this.georasters.every((georaster: GeoRaster) => typeof georaster.values === "object")) {
        this.rasters = this.georasters.reduce((result: number[][][], georaster: GeoRaster) => {
          // added double-check of values to make typescript linter and compiler happy
          if (georaster.values) {
            result = result.concat(georaster.values);
            return result;
          }
        }, []);
        if (this.debugLevel > 1) console.log("this.rasters:", this.rasters);
      }

      if (options.mask) {
        if (typeof options.mask === "string") {
          this.mask = fetch(options.mask).then(r => r.json()) as Promise<Mask>;
        } else if (typeof options.mask === "object") {
          this.mask = Promise.resolve(options.mask);
        }

        // default mask srs is the EPSG:4326 projection used by GeoJSON
        this.mask_srs = options.mask_srs || "EPSG:4326";
      }

      this.mask_strategy = (options.mask_strategy || "outside") as MaskStrategy;

      this.chroma = chroma;
      this.scale = chroma.scale();

      // could probably replace some day with a simple
      // (for let k in options) { this.options[k] = options[k]; }
      // but need to find a way around TypeScript any issues
      L.Util.setOptions(this, options);

      /*
          Caching the constant tile size, so we don't recalculate everytime we
          create a new tile
      */
      const tileSize = this.getTileSize();
      this.tileHeight = tileSize.y;
      this.tileWidth = tileSize.x;

      if (this.georasters.length >= 4 && !options.pixelValuesToColorFn && !options.rasterIndex) {
        throw "you must pass in a pixelValuesToColorFn if you are combining rasters";
      }

      // total number of bands across all georasters
      this.numBands = this.georasters.reduce((total: number, g: GeoRaster) => total + g.numberOfRasters, 0);
      if (this.debugLevel > 1) console.log("this.numBands:", this.numBands);

      // in-case we want to track dynamic/running stats of all pixels fetched
      this.currentStats = {
        mins: new Array(this.numBands),
        maxs: new Array(this.numBands),
        ranges: new Array(this.numBands)
      };
    } catch (error) {
      console.error("ERROR initializing GeoTIFFLayer", error);
    }
  },

  onAdd: function (map: any) {
    if (!this.options.maxZoom) {
      // maxZoom is needed to display the tiles in the correct order over the zIndex between the zoom levels
      // https://github.com/Leaflet/Leaflet/blob/2592967aa6bd392db0db9e58dab840054e2aa291/src/layer/tile/GridLayer.js#L375C21-L375C21
      this.options.maxZoom = map.getMaxZoom();
    }

    L.GridLayer.prototype.onAdd.call(this, map);
  },

  getRasters: function (options: GetRasterOptions) {
    const {
      innerTileTopLeftPoint,
      heightOfSampleInScreenPixels,
      widthOfSampleInScreenPixels,
      zoom,
      numberOfSamplesAcross,
      numberOfSamplesDown,
      ymax,
      xmin
    } = options;
    if (this.debugLevel >= 1) console.log("starting getRasters with options:", options);

    // called if georaster was constructed from URL and we need to get
    // data separately for each tile
    // aka 'COG mode'

    /*
      This function takes in coordinates in the rendered image inner tile and
      returns the y and x values in the original raster
    */
    const rasterCoordsForTileCoords = (h: number, w: number): { x: number; y: number } | null => {
      const xInMapPixels = innerTileTopLeftPoint.x + w * widthOfSampleInScreenPixels;
      const yInMapPixels = innerTileTopLeftPoint.y + h * heightOfSampleInScreenPixels;

      const mapPoint = L.point(xInMapPixels, yInMapPixels);
      if (this.debugLevel >= 1) log({ mapPoint });

      const { lat, lng } = this.getMap().unproject(mapPoint, zoom);

      if (this.projection === EPSG4326) {
        return {
          y: Math.round((ymax - lat) / this.pixelHeight),
          x: Math.round((lng - xmin) / this.pixelWidth)
        };
      } else if (this.getProjector()) {
        /* source raster doesn't use latitude and longitude,
           so need to reproject point from lat/long to projection of raster
        */
        const [x, y] = this.getProjector().inverse([lng, lat]);
        if (x === Infinity || y === Infinity) {
          if (this.debugLevel >= 1) console.error("projector converted", [lng, lat], "to", [x, y]);
        }
        return {
          y: Math.round((ymax - y) / this.pixelHeight),
          x: Math.round((x - xmin) / this.pixelWidth)
        };
      } else {
        return null;
      }
    };

    // careful not to flip min_y/max_y here
    const topLeft = rasterCoordsForTileCoords(0, 0);
    const bottomRight = rasterCoordsForTileCoords(numberOfSamplesDown, numberOfSamplesAcross);

    const getValuesOptions = {
      bottom: bottomRight?.y,
      height: numberOfSamplesDown,
      left: topLeft?.x,
      right: bottomRight?.x,
      top: topLeft?.y,
      width: numberOfSamplesAcross
    };

    if (!Object.values(getValuesOptions).every(it => it !== undefined && isFinite(it))) {
      console.error("getRasters failed because not all values are finite:", getValuesOptions);
    } else {
      // !note: The types need confirmation - SFR 2021-01-20
      return Promise.all(
        this.georasters.map((georaster: GeoRaster) =>
          georaster.getValues({ ...getValuesOptions, resampleMethod: this.resampleMethod || "nearest" })
        )
      ).then(valuesByGeoRaster =>
        valuesByGeoRaster.reduce((result: number[][][], values) => {
          result = result.concat(values as number[][]);
          return result;
        }, [])
      );
    }
  },

  createTile: function (coords: Coords, done: DoneCallback) {
    /* This tile is the square piece of the Leaflet map that we draw on */
    const tile = L.DomUtil.create("canvas", "leaflet-tile") as HTMLCanvasElement;

    // we do this because sometimes css normalizers will set * to box-sizing: border-box
    tile.style.boxSizing = "content-box";

    // start tile hidden
    tile.style.visibility = "hidden";

    const context = tile.getContext("2d");

    // note that we aren't setting the tile height or width here
    // drawTile dynamically sets the width and padding based on
    // how much the georaster takes up the tile area
    const coordsKey = this._tileCoordsToKey(coords);

    const resolution = this._getResolution(coords.z);
    const urls: string = this.georasters.reduce((acc: string, val: GeoRaster) => {
      const url = val._url;
      if (acc === "") {
        return url;
      } else {
        return `${acc}:${url}`;
      }
    }, "");
    const key = `${urls}:${this.rasterIndex}:${coordsKey}:${resolution}`;
    const doneCb = (error?: Error, tile?: HTMLCanvasElement): void => {
      done(error, tile);

      // caching the rendered tile, to skip the calculation for the next time
      if (!error && this.options.caching && tile) {
        if (!(key in this.cache)) this.cache[key] = tile;
        db.cachedTiles.get({ key }).then(cachedTile => {
          if (!cachedTile) {
            db.cachedTiles.put({ key, tile: tile.toDataURL() }).catch(error => {
              console.error("Error writing tile to cache:", error);
            });
          }
        });
      }
    };

    const drawTileParams = {
      tile, coords, context, done: doneCb, resolution
    };

    if (this.options.caching) {
      if (key in this.cache) {
        if (this.debugLevel >= 2) console.log(`memory cache hit for tile ${key}`);
        done(undefined, this.cache[key]);
        return this.cache[key];
      } else {
        db.cachedTiles.get({ key })
          .then(cachedTile => {
            if (cachedTile) {
              if (this.debugLevel >= 2) console.log(`indexeddb cache hit for tile ${key}`);
              const img = new Image();
              img.onload = () => {
                if (context) context.drawImage(img, 0, 0);
                tile.style.visibility = "visible";
              };
              img.src = cachedTile.tile;
              this.cache[key] = tile;
              done(undefined, tile);
            } else {
              this.drawTile(drawTileParams);
            }
          })
          .catch(error => {
            console.error("Error reading tile from cache:", error);
            this.drawTile(drawTileParams);
          });
      }
    } else {
      this.drawTile(drawTileParams);
    }

    return tile;
  },

  drawTile: function ({ tile, coords, context, done, resolution }: DrawTileOptions) {
    try {
      const { debugLevel = 0 } = this;

      if (debugLevel >= 2) console.log("starting drawTile with", { tile, coords, context, done });

      let error: Error;

      const { z: zoom } = coords;

      // stringified hash of tile coordinates for caching purposes
      const cacheKey = [coords.x, coords.y, coords.z].join(",");
      if (debugLevel >= 2) log({ cacheKey });

      const mapCRS = this.getMapCRS();
      if (debugLevel >= 2) log({ mapCRS });

      const inSimpleCRS = isSimpleCRS(mapCRS);
      if (debugLevel >= 2) log({ inSimpleCRS });

      // Unpacking values for increased speed
      const { rasters, xmin, xmax, ymin, ymax } = this;
      const rasterHeight = this.height;
      const rasterWidth = this.width;

      const extentOfLayer = new GeoExtent(this.getBounds(), { srs: inSimpleCRS ? "simple" : 4326 });
      if (debugLevel >= 2) log({ extentOfLayer });

      const pixelHeight = inSimpleCRS ? extentOfLayer.height / rasterHeight : this.pixelHeight;
      const pixelWidth = inSimpleCRS ? extentOfLayer.width / rasterWidth : this.pixelWidth;
      if (debugLevel >= 2) log({ pixelHeight, pixelWidth });

      const boundsOfTile = this._tileCoordsToBounds(coords);
      if (debugLevel >= 2) log({ boundsOfTile });

      const { code } = mapCRS;
      if (debugLevel >= 2) log({ code });
      const extentOfTile = new GeoExtent(boundsOfTile, { srs: inSimpleCRS ? "simple" : 4326 });
      if (debugLevel >= 2) log({ extentOfTile });

      // create blue outline around tiles
      if (debugLevel >= 4) {
        if (!this._cache.tile[cacheKey]) {
          this._cache.tile[cacheKey] = L.rectangle(extentOfTile.leafletBounds, { fillOpacity: 0 })
            .addTo(this.getMap())
            .bindTooltip(cacheKey, { direction: "center", permanent: true });
        }
      }

      const extentOfTileInMapCRS = inSimpleCRS ? extentOfTile : extentOfTile.reproj(code);
      if (debugLevel >= 2) log({ extentOfTileInMapCRS });

      let extentOfInnerTileInMapCRS = extentOfTileInMapCRS.crop(inSimpleCRS ? extentOfLayer : this.extent);
      if (debugLevel >= 2)
        console.log(
          "[georaster-layer-for-leaflet] extentOfInnerTileInMapCRS",
          extentOfInnerTileInMapCRS.reproj(inSimpleCRS ? "simple" : 4326)
        );
      if (debugLevel >= 2) log({ coords, extentOfInnerTileInMapCRS, extent: this.extent });

      // create blue outline around tiles
      if (debugLevel >= 4) {
        if (!this._cache.innerTile[cacheKey]) {
          const ext = inSimpleCRS ? extentOfInnerTileInMapCRS : extentOfInnerTileInMapCRS.reproj(4326);
          this._cache.innerTile[cacheKey] = L.rectangle(ext.leafletBounds, {
            color: "#F00",
            dashArray: "5, 10",
            fillOpacity: 0
          }).addTo(this.getMap());
        }
      }

      const widthOfScreenPixelInMapCRS = extentOfTileInMapCRS.width / this.tileWidth;
      const heightOfScreenPixelInMapCRS = extentOfTileInMapCRS.height / this.tileHeight;
      if (debugLevel >= 3) log({ heightOfScreenPixelInMapCRS, widthOfScreenPixelInMapCRS });

      // expand tile sampling area to align with raster pixels
      const oldExtentOfInnerTileInRasterCRS = inSimpleCRS
        ? extentOfInnerTileInMapCRS
        : extentOfInnerTileInMapCRS.reproj(this.projection);
      const snapped = snap({
        bbox: oldExtentOfInnerTileInRasterCRS.bbox,
        // pad xmax and ymin of container to tolerate ceil() and floor() in snap()
        container: inSimpleCRS
          ? [
            extentOfLayer.xmin,
            extentOfLayer.ymin - 0.25 * pixelHeight,
            extentOfLayer.xmax + 0.25 * pixelWidth,
            extentOfLayer.ymax
          ]
          : [xmin, ymin - 0.25 * pixelHeight, xmax + 0.25 * pixelWidth, ymax],
        debug: debugLevel >= 2,
        origin: inSimpleCRS ? [extentOfLayer.xmin, extentOfLayer.ymax] : [xmin, ymax],
        scale: [pixelWidth, -pixelHeight] // negative because origin is at ymax
      });
      const extentOfInnerTileInRasterCRS = new GeoExtent(snapped.bbox_in_coordinate_system, {
        srs: inSimpleCRS ? "simple" : this.projection
      });

      const gridbox = snapped.bbox_in_grid_cells;
      const snappedSamplesAcross = Math.abs(gridbox[2] - gridbox[0]);
      const snappedSamplesDown = Math.abs(gridbox[3] - gridbox[1]);
      const rasterPixelsAcross = Math.ceil(oldExtentOfInnerTileInRasterCRS.width / pixelWidth);
      const rasterPixelsDown = Math.ceil(oldExtentOfInnerTileInRasterCRS.height / pixelHeight);
      const layerCropExtent = inSimpleCRS ? extentOfLayer : this.extent;
      const recropTileOrig = oldExtentOfInnerTileInRasterCRS.crop(layerCropExtent); // may be null
      let maxSamplesAcross = 1;
      let maxSamplesDown = 1;
      if (recropTileOrig !== null) {
        const recropTileProj = inSimpleCRS ? recropTileOrig : recropTileOrig.reproj(code);
        const recropTile = recropTileProj.crop(extentOfTileInMapCRS);
        if (recropTile !== null) {
          maxSamplesAcross = Math.ceil(resolution * (recropTile.width / extentOfTileInMapCRS.width));
          maxSamplesDown = Math.ceil(resolution * (recropTile.height / extentOfTileInMapCRS.height));
        }
      }

      const overdrawTileAcross = rasterPixelsAcross < maxSamplesAcross;
      const overdrawTileDown = rasterPixelsDown < maxSamplesDown;
      const numberOfSamplesAcross = overdrawTileAcross ? snappedSamplesAcross : maxSamplesAcross;
      const numberOfSamplesDown = overdrawTileDown ? snappedSamplesDown : maxSamplesDown;

      if (debugLevel >= 3)
        console.log(
          "[georaster-layer-for-leaflet] extent of inner tile before snapping " +
            extentOfInnerTileInMapCRS.reproj(inSimpleCRS ? "simple" : 4326).bbox.toString()
        );

      // Reprojecting the bounding box back to the map CRS would expand it
      // (unless the projection is purely scaling and translation),
      // so instead just extend the old map bounding box proportionately.
      {
        const oldrb = new GeoExtent(oldExtentOfInnerTileInRasterCRS.bbox);
        const newrb = new GeoExtent(extentOfInnerTileInRasterCRS.bbox);
        const oldmb = new GeoExtent(extentOfInnerTileInMapCRS.bbox);
        if (oldrb.width !== 0 && oldrb.height !== 0) {
          let n0 = ((newrb.xmin - oldrb.xmin) / oldrb.width) * oldmb.width;
          let n1 = ((newrb.ymin - oldrb.ymin) / oldrb.height) * oldmb.height;
          let n2 = ((newrb.xmax - oldrb.xmax) / oldrb.width) * oldmb.width;
          let n3 = ((newrb.ymax - oldrb.ymax) / oldrb.height) * oldmb.height;
          if (!overdrawTileAcross) {
            n0 = Math.max(n0, 0);
            n2 = Math.min(n2, 0);
          }
          if (!overdrawTileDown) {
            n1 = Math.max(n1, 0);
            n3 = Math.min(n3, 0);
          }
          const newbox = [oldmb.xmin + n0, oldmb.ymin + n1, oldmb.xmax + n2, oldmb.ymax + n3];
          extentOfInnerTileInMapCRS = new GeoExtent(newbox, { srs: extentOfInnerTileInMapCRS.srs });
        }
      }

      // create outline around raster pixels
      if (debugLevel >= 4) {
        if (!this._cache.innerTile[cacheKey]) {
          const ext = inSimpleCRS ? extentOfInnerTileInMapCRS : extentOfInnerTileInMapCRS.reproj(4326);
          this._cache.innerTile[cacheKey] = L.rectangle(ext.leafletBounds, {
            color: "#F00",
            dashArray: "5, 10",
            fillOpacity: 0
          }).addTo(this.getMap());
        }
      }

      if (debugLevel >= 3)
        console.log(
          "[georaster-layer-for-leaflet] extent of inner tile after snapping " +
            extentOfInnerTileInMapCRS.reproj(inSimpleCRS ? "simple" : 4326).bbox.toString()
        );

      // Note that the snapped "inner" tile may extend beyond the original tile,
      // in which case the padding values will be negative.

      // we round here because sometimes there will be slight floating arithmetic issues
      // where the padding is like 0.00000000000001
      const padding = {
        left: Math.round((extentOfInnerTileInMapCRS.xmin - extentOfTileInMapCRS.xmin) / widthOfScreenPixelInMapCRS),
        right: Math.round((extentOfTileInMapCRS.xmax - extentOfInnerTileInMapCRS.xmax) / widthOfScreenPixelInMapCRS),
        top: Math.round((extentOfTileInMapCRS.ymax - extentOfInnerTileInMapCRS.ymax) / heightOfScreenPixelInMapCRS),
        bottom: Math.round((extentOfInnerTileInMapCRS.ymin - extentOfTileInMapCRS.ymin) / heightOfScreenPixelInMapCRS)
      };
      if (debugLevel >= 3) log({ padding });

      const innerTileHeight = this.tileHeight - padding.top - padding.bottom;
      const innerTileWidth = this.tileWidth - padding.left - padding.right;
      if (debugLevel >= 3) log({ innerTileHeight, innerTileWidth });

      if (debugLevel >= 4) {
        const xMinOfInnerTileInMapCRS = extentOfTileInMapCRS.xmin + padding.left * widthOfScreenPixelInMapCRS;
        const yMinOfInnerTileInMapCRS = extentOfTileInMapCRS.ymin + padding.bottom * heightOfScreenPixelInMapCRS;
        const xMaxOfInnerTileInMapCRS = extentOfTileInMapCRS.xmax - padding.right * widthOfScreenPixelInMapCRS;
        const yMaxOfInnerTileInMapCRS = extentOfTileInMapCRS.ymax - padding.top * heightOfScreenPixelInMapCRS;
        log({ xMinOfInnerTileInMapCRS, yMinOfInnerTileInMapCRS, xMaxOfInnerTileInMapCRS, yMaxOfInnerTileInMapCRS });
      }

      const canvasPadding = {
        left: Math.max(padding.left, 0),
        right: Math.max(padding.right, 0),
        top: Math.max(padding.top, 0),
        bottom: Math.max(padding.bottom, 0)
      };
      const canvasHeight = this.tileHeight - canvasPadding.top - canvasPadding.bottom;
      const canvasWidth = this.tileWidth - canvasPadding.left - canvasPadding.right;

      // set padding and size of canvas tile
      tile.style.paddingTop = canvasPadding.top + "px";
      tile.style.paddingRight = canvasPadding.right + "px";
      tile.style.paddingBottom = canvasPadding.bottom + "px";
      tile.style.paddingLeft = canvasPadding.left + "px";

      tile.height = canvasHeight;
      tile.style.height = canvasHeight + "px";

      tile.width = canvasWidth;
      tile.style.width = canvasWidth + "px";
      if (debugLevel >= 3) console.log("setting tile height to " + canvasHeight + "px");
      if (debugLevel >= 3) console.log("setting tile width to " + canvasWidth + "px");

      // set how large to display each sample in screen pixels
      const heightOfSampleInScreenPixels = innerTileHeight / numberOfSamplesDown;
      const heightOfSampleInScreenPixelsInt = Math.ceil(heightOfSampleInScreenPixels);
      const widthOfSampleInScreenPixels = innerTileWidth / numberOfSamplesAcross;
      const widthOfSampleInScreenPixelsInt = Math.ceil(widthOfSampleInScreenPixels);

      const tileSize = this.getTileSize();

      // this converts tile coordinates (how many tiles down and right)
      // to pixels from left and top of tile pane
      const tileNwPoint = coords.scaleBy(tileSize);
      if (debugLevel >= 4) log({ tileNwPoint });
      const xLeftOfInnerTile = tileNwPoint.x + padding.left;
      const yTopOfInnerTile = tileNwPoint.y + padding.top;
      const innerTileTopLeftPoint = { x: xLeftOfInnerTile, y: yTopOfInnerTile };
      if (debugLevel >= 4) log({ innerTileTopLeftPoint });

      // render asynchronously so tiles show up as they finish instead of all at once (which blocks the UI)
      setTimeout(async () => {
        let timerId;
        if (debugLevel >= 2) {
          timerId = uuidv4();
          console.time(timerId);
        }
        const imageData = new ImageData(tileSize.x, tileSize.y);
        const data = imageData.data;
        try {
          let tileRasters: number[][][] | null = null;
          if (!rasters) {
            tileRasters = await this.getRasters({
              innerTileTopLeftPoint,
              heightOfSampleInScreenPixels,
              widthOfSampleInScreenPixels,
              zoom,
              pixelHeight,
              pixelWidth,
              numberOfSamplesAcross,
              numberOfSamplesDown,
              ymax,
              xmin
            });
            if (tileRasters && this.calcStats) {
              const { noDataValue } = this;
              for (let bandIndex = 0; bandIndex < tileRasters.length; bandIndex++) {
                let min = this.currentStats.mins[bandIndex];
                let max = this.currentStats.maxs[bandIndex];
                const band = tileRasters[bandIndex];
                for (let rowIndex = 0; rowIndex < band.length; rowIndex++) {
                  const row = band[rowIndex];
                  for (let columnIndex = 0; columnIndex < row.length; columnIndex++) {
                    const value = row[columnIndex];
                    if (value !== noDataValue) {
                      if (min === undefined || value < min) {
                        min = value;
                      }
                      if (max === undefined || value > max) {
                        max = value;
                      }
                    }
                  }
                }
                this.currentStats.mins[bandIndex] = min;
                this.currentStats.maxs[bandIndex] = max;
                this.currentStats.ranges[bandIndex] = max - min;
              }
            }
            if (this._dynamic) {
              try {
                const rawToRgbFn = (rawToRgb as any).default || rawToRgb;
                this.rawToRgb = rawToRgbFn({
                  format: "string",
                  flip: this.currentStats.mins.length === 1 ? true : false,
                  ranges: zip(this.currentStats.mins, this.currentStats.maxs),
                  round: true
                });
              } catch (error) {
                console.error(error);
              }
            }
          }

          if (this.isYCbCr === undefined) {
            const image = await this.georasters[0]._geotiff?.getImage();
            this.isYCbCr = image?.fileDirectory?.PhotometricInterpretation === YCBCR_INTERP;
          }

          for (let h = 0; h < numberOfSamplesDown; h++) {
            const yInTilePixels = Math.round(h * heightOfSampleInScreenPixels) + Math.min(padding.top, 0);

            for (let w = 0; w < numberOfSamplesAcross; w++) {
              let values = null;
              if (tileRasters) {
                // get value from array specific to this tile
                values = tileRasters.map(band => band[h][w]);
              } else {
                done && done(Error("no rasters are available for, so skipping value generation"));
                return;
              }

              // x-axis coordinate of the starting point of the rectangle representing the raster pixel
              const x = Math.round(w * widthOfSampleInScreenPixels) + Math.min(padding.left, 0);

              // y-axis coordinate of the starting point of the rectangle representing the raster pixel
              const y = yInTilePixels;

              // how many real screen pixels does a pixel of the sampled raster take up
              const width = widthOfSampleInScreenPixelsInt;
              const height = heightOfSampleInScreenPixelsInt;

              if (this.options.customDrawFunction) {
                this.options.customDrawFunction({
                  values,
                  context,
                  x,
                  y,
                  width,
                  height,
                  sampleX: w,
                  sampleY: h,
                  sampledRaster: tileRasters
                });
              } else {
                let r;
                let g;
                let b;
                let a = 255;
                if (this.options.pixelValuesToColorFn) {
                  [r, g, b, a] = this.options.pixelValuesToColorFn(values);
                } else {
                  const numberOfValues = values.length;
                  let haveDataForAllBands = true;
                  for (const value of values) {
                    if (value === undefined || value === this.noDataValue) {
                      haveDataForAllBands = false;
                      break;
                    }
                  }
                  if (haveDataForAllBands) {
                    if (numberOfValues === 1 || this.rasterIndex !== undefined) {
                      const value = values[this.rasterIndex ?? 0];
                      const normValue = Math.max(RGB_MIN, Math.min(RGB_MAX, Math.round((value - this.minValues[0]) / (this.maxValues[0] - this.minValues[0]) * RGB_MAX)));
                      r = normValue;
                      g = normValue;
                      b = normValue;
                    } else if (numberOfValues === 2) {
                      r = values[0];
                      g = values[1];
                      b = 0;
                    } else if (numberOfValues === 3) {
                      r = Math.max(RGB_MIN, Math.min(RGB_MAX, Math.round((values[0] - this.minValues[0]) / (this.maxValues[0] - this.minValues[0]) * RGB_MAX)));
                      g = Math.max(RGB_MIN, Math.min(RGB_MAX, Math.round((values[1] - this.minValues[0]) / (this.maxValues[0] - this.minValues[0]) * RGB_MAX)));
                      b = Math.max(RGB_MIN, Math.min(RGB_MAX, Math.round((values[2] - this.minValues[0]) / (this.maxValues[0] - this.minValues[0]) * RGB_MAX)));
                      if (this.isYCbCr) {
                        const [rOld, gOld, bOld] = [r, g, b];
                        r = Math.round(rOld + 1.402 * (bOld - 0x80));
                        g = Math.round(rOld - 0.34414 * (gOld - 0x80) - 0.71414 * (bOld - 0x80));
                        b = Math.round(rOld + 1.772 * (gOld - 0x80));
                      }
                    } else if (numberOfValues === 4) {
                      r = values[0];
                      g = values[1];
                      b = values[2];
                      a = values[3] / 255;
                    }
                  }
                }

                if (r !== undefined && g !== undefined && b !== undefined && a !== undefined) {
                  for (let dy = 0; dy < height; dy++) {
                    for (let dx = 0; dx < width; dx++) {
                      const index = ((y + dy) * tileSize.x + (x + dx)) * 4;
                      data[index + 0] = r;
                      data[index + 1] = g;
                      data[index + 2] = b;
                      data[index + 3] = a;
                    }
                  }
                }
              }
            }
          }

          if (this.mask) {
            if (inSimpleCRS) {
              console.warn("[georaster-layer-for-leaflet] mask is not supported when using simple projection");
            } else {
              this.mask.then((mask: Mask) => {
                geocanvas.maskCanvas({
                  canvas: tile,
                  // eslint-disable-next-line camelcase
                  canvas_bbox: extentOfInnerTileInMapCRS.bbox, // need to support simple projection too
                  // eslint-disable-next-line camelcase
                  canvas_srs: 3857, // default map crs, need to support simple
                  mask,
                  // eslint-disable-next-line camelcase
                  mask_srs: this.mask_srs,
                  strategy: this.mask_strategy // hide everything inside or outside the mask
                });
              });
            }
          }

          if (context) context.putImageData(imageData, 0, 0);
          tile.style.visibility = "visible"; // set to default
        } catch (e: any) {
          console.error(e);
          error = e;
        }
        done && done(error, tile);
        if (this.debugLevel >= 2) console.timeEnd(timerId);
      }, 0);

      // return the tile so it can be rendered on screen
      return tile;
    } catch (error: any) {
      console.error(error);
      done && done(error, tile);
    }
  },

  // copied from Leaflet with slight modifications,
  // including removing the lines that set the tile size
  _initTile: function (tile: HTMLCanvasElement) {
    L.DomUtil.addClass(tile, "leaflet-tile");

    tile.onselectstart = L.Util.falseFn;
    tile.onmousemove = L.Util.falseFn;

    // update opacity on tiles in IE7-8 because of filter inheritance problems
    if (L.Browser.ielt9 && this.options.opacity < 1) {
      L.DomUtil.setOpacity(tile, this.options.opacity);
    }

    // without this hack, tiles disappear after zoom on Chrome for Android
    // https://github.com/Leaflet/Leaflet/issues/2078
    if (L.Browser.android && !L.Browser.android23) {
      (<CustomCSSStyleDeclaration>tile.style).WebkitBackfaceVisibility = "hidden";
    }
  },

  // method from https://github.com/Leaflet/Leaflet/blob/bb1d94ac7f2716852213dd11563d89855f8d6bb1/src/layer/ImageOverlay.js
  getBounds: function () {
    this.initBounds();
    return this._bounds;
  },

  getMap: function () {
    return this._map || this._mapToAdd;
  },

  getMapCRS: function () {
    return this.getMap()?.options.crs || L.CRS.EPSG3857;
  },

  // add in to ensure backwards compatability with Leaflet 1.0.3
  _tileCoordsToNwSe: function (coords: Coords) {
    const map = this.getMap();
    const tileSize = this.getTileSize();
    const nwPoint = coords.scaleBy(tileSize);
    const sePoint = nwPoint.add(tileSize);
    const nw = map.unproject(nwPoint, coords.z);
    const se = map.unproject(sePoint, coords.z);
    return [nw, se];
  },

  _tileCoordsToBounds: function (coords: Coords) {
    const [nw, se] = this._tileCoordsToNwSe(coords);
    let bounds: LatLngBounds = new L.LatLngBounds(nw, se);

    if (!this.options.noWrap) {
      const { crs } = this.getMap().options;
      bounds = crs.wrapLatLngBounds(bounds);
    }
    return bounds;
  },

  _isValidTile: function (coords: Coords) {
    const crs = this.getMapCRS();

    if (!crs.infinite) {
      // don't load tile if it's out of bounds and not wrapped
      const globalBounds = this._globalTileRange;
      if (
        (!crs.wrapLng && (coords.x < globalBounds.min.x || coords.x > globalBounds.max.x)) ||
        (!crs.wrapLat && (coords.y < globalBounds.min.y || coords.y > globalBounds.max.y))
      ) {
        return false;
      }
    }

    const bounds = this.getBounds();

    if (!bounds) {
      return true;
    }

    const { x, y, z } = coords;

    // not sure what srs should be here when simple crs
    const layerExtent = new GeoExtent(bounds, { srs: 4326 });

    const boundsOfTile = this._tileCoordsToBounds(coords);

    // check given tile coordinates
    if (layerExtent.overlaps(boundsOfTile)) return true;

    // if not within the original confines of the earth return false
    // we don't want wrapping if using Simple CRS
    if (isSimpleCRS(crs)) return false;

    // width of the globe in tiles at the given zoom level
    const width = Math.pow(2, z);

    // check one world to the left
    const leftCoords = L.point(x - width, y) as Coords;
    leftCoords.z = z;
    const leftBounds = this._tileCoordsToBounds(leftCoords);
    if (layerExtent.overlaps(leftBounds)) return true;

    // check one world to the right
    const rightCoords = L.point(x + width, y) as Coords;
    rightCoords.z = z;
    const rightBounds = this._tileCoordsToBounds(rightCoords);
    if (layerExtent.overlaps(rightBounds)) return true;

    return false;
  },

  /**
   * Redraws the active map tiles updating the pixel values using the supplie callback
   */
  updateColors(
    pixelValuesToColorFn: /**The callback used to determine the colour based on the values of each pixel */ PixelValuesToColorFn,
    { debugLevel = -1 } = { debugLevel: -1 }
  ) {
    if (!pixelValuesToColorFn) {
      throw new Error("Missing pixelValuesToColorFn function");
    }

    // if debugLevel is -1, set it to the default for the class
    if (debugLevel === -1) debugLevel = this.debugLevel;

    if (debugLevel >= 1) console.log("Start updating active tile pixel values");

    // update option to ensure correct colours at other zoom levels.
    this.options.pixelValuesToColorFn = pixelValuesToColorFn;

    const tiles = this.getActiveTiles();
    if (!tiles) {
      console.error("No active tiles available");
      return this;
    }

    if (debugLevel >= 1) console.log("Active tiles fetched", tiles);

    tiles.forEach((tile: Tile) => {
      const { coords, el } = tile;
      this.drawTile({ tile: el, coords, context: el.getContext("2d") });
    });
    if (debugLevel >= 1) console.log("Finished updating active tile colours");
    return this;
  },

  getTiles(): Tile[] {
    // transform _tiles object collection into an array
    return Object.values(this._tiles);
  },

  getActiveTiles(): Tile[] {
    const tiles: Tile[] = this.getTiles();
    // only return valid tiles
    return tiles.filter(tile => this._isValidTile(tile.coords));
  },

  isSupportedProjection: function () {
    if (this._isSupportedProjection === undefined) {
      const projection = this.projection;
      if (isUTM(projection)) {
        this._isSupportedProjection = true;
      } else if (PROJ4_SUPPORTED_PROJECTIONS.has(projection)) {
        this._isSupportedProjection = true;
      } else if (typeof proj4FullyLoaded === "function" && `EPSG:${projection}` in proj4FullyLoaded.defs) {
        this._isSupportedProjection = true;
      } else if (
        typeof proj4 === "function" &&
        typeof proj4.defs !== "undefined" &&
        `EPSG:${projection}` in proj4.defs
      ) {
        this._isSupportedProjection = true;
      } else {
        this._isSupportedProjection = false;
      }
    }
    return this._isSupportedProjection;
  },

  getProjectionString: function (projection: number) {
    if (isUTM(projection)) {
      return getProjString(projection);
    }
    return `EPSG:${projection}`;
  },

  initBounds: function (options: GeoRasterLayerOptions) {
    if (!options) options = this.options;
    if (!this._bounds) {
      const { debugLevel, height, width, projection, xmin, xmax, ymin, ymax } = this;
      // check if map using Simple CRS
      if (isSimpleCRS(this.getMapCRS())) {
        if (height === width) {
          this._bounds = L.latLngBounds([ORIGIN, [MAX_NORTHING, MAX_EASTING]]);
        } else if (height > width) {
          this._bounds = L.latLngBounds([ORIGIN, [MAX_NORTHING, MAX_EASTING / this.ratio]]);
        } else if (width > height) {
          this._bounds = L.latLngBounds([ORIGIN, [MAX_NORTHING * this.ratio, MAX_EASTING]]);
        }
      } else if (projection === EPSG4326) {
        if (debugLevel >= 1) console.log(`georaster projection is in ${EPSG4326}`);
        const minLatWest = L.latLng(ymin, xmin);
        const maxLatEast = L.latLng(ymax, xmax);
        this._bounds = L.latLngBounds(minLatWest, maxLatEast);
      } else if (this.getProjector()) {
        if (debugLevel >= 1) console.log("projection is UTM or supported by proj4");
        const bottomLeft = this.getProjector().forward({ x: xmin, y: ymin });
        const minLatWest = L.latLng(bottomLeft.y, bottomLeft.x);
        const topRight = this.getProjector().forward({ x: xmax, y: ymax });
        const maxLatEast = L.latLng(topRight.y, topRight.x);
        this._bounds = L.latLngBounds(minLatWest, maxLatEast);
      } else {
        if (typeof proj4FullyLoaded !== "function") {
          throw `You are using the lite version of georaster-layer-for-leaflet, which does not support rasters with the projection ${projection}.  Please try using the default build or add the projection definition to your global proj4.`;
        } else {
          throw `GeoRasterLayer does not provide built-in support for rasters with the projection ${projection}.  Add the projection definition to your global proj4.`;
        }
      }

      // these values are used so we don't try to sample outside of the raster
      this.xMinOfLayer = this._bounds.getWest();
      this.xMaxOfLayer = this._bounds.getEast();
      this.yMaxOfLayer = this._bounds.getNorth();
      this.yMinOfLayer = this._bounds.getSouth();

      options.bounds = this._bounds;
    }
  },

  getProjector: function () {
    if (this.isSupportedProjection()) {
      if (!proj4FullyLoaded && !proj4) {
        throw "proj4 must be found in the global scope in order to load a raster that uses this projection";
      }
      if (!this._projector) {
        const projString = this.getProjectionString(this.projection);
        if (this.debugLevel >= 1) log({ projString });
        let proj4Lib;
        if (projString.startsWith("EPSG")) {
          if (typeof proj4 === "function" && typeof proj4.defs === "function" && projString in proj4.defs) {
            proj4Lib = proj4;
          } else if (
            typeof proj4FullyLoaded === "function" &&
            typeof proj4FullyLoaded.defs === "function" &&
            projString in proj4FullyLoaded.defs
          ) {
            proj4Lib = proj4FullyLoaded;
          } else {
            throw "[georaster-layer-for-leaflet] projection not found in proj4 instance";
          }
        } else {
          if (typeof proj4 === "function") {
            proj4Lib = proj4;
          } else if (typeof proj4FullyLoaded === "function") {
            proj4Lib = proj4FullyLoaded;
          } else {
            throw "[georaster-layer-for-leaflet] projection not found in proj4 instance";
          }
        }
        this._projector = proj4Lib(projString, `EPSG:${EPSG4326}`);

        if (this.debugLevel >= 1) console.log("projector set");
      }
      return this._projector;
    }
  },

  same(array: GeoRaster[], key: GeoRasterKeys) {
    return new Set(array.map(item => item[key])).size === 1;
  },

  clearCache() {
    this.cache = {};
  },

  _getResolution(zoom: number) {
    const { resolution } = this.options;

    let resolutionValue;
    if (typeof resolution === "object") {
      const zoomLevels = Object.keys(resolution);

      for (const key in zoomLevels) {
        if (Object.prototype.hasOwnProperty.call(zoomLevels, key)) {
          const zoomLvl = parseInt(zoomLevels[key]);
          if (zoomLvl <= zoom) {
            resolutionValue = resolution[zoomLvl];
          } else {
            break;
          }
        }
      }
    } else {
      resolutionValue = resolution;
    }

    return resolutionValue;
  }
});

/* eslint-disable @typescript-eslint/no-explicit-any */
if (typeof window === "object") {
  (window as any)["GeoRasterLayer"] = GeoRasterLayer;
}
if (typeof self !== "undefined") {
  (self as any)["GeoRasterLayer"] = GeoRasterLayer;
}
/* eslint-enable @typescript-eslint/no-explicit-any */

export default GeoRasterLayer;

// Explicitly exports public types
export type { GeoRaster, GeoRasterLayerOptions, PixelValuesToColorFn } from "./types";
