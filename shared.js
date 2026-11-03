// Спільний код: категорії, генерація catalog.data, потоковий SHA-256.
(function (root) {
  "use strict";

  // name = значення для modN_category (його чекає гра)
  const CATEGORIES = [
    { name: "tractorsS", title: "Трактори малі" },
    { name: "tractorsM", title: "Трактори середні" },
    { name: "tractorsL", title: "Трактори великі" },
    { name: "trucks", title: "Вантажівки" },
    { name: "cars", title: "Легкові та пікапи" },
    { name: "harvesters", title: "Комбайни" },
    { name: "wheelLoaderVehicles", title: "Навантажувачі" },
    { name: "frontLoaders", title: "Фронтальні навантажувачі" },
    { name: "trailers", title: "Причепи" },
    { name: "plows", title: "Плуги" },
    { name: "cultivators", title: "Культиватори" },
    { name: "seeders", title: "Сівалки" },
    { name: "sprayers", title: "Обприскувачі" },
    { name: "fertilizerSpreaders", title: "Розкидачі добрив" },
    { name: "manureSpreaders", title: "Розкидачі гною" },
    { name: "slurryTanks", title: "Цистерни для гноївки" },
    { name: "mowers", title: "Косарки" },
    { name: "balers", title: "Прес-підбирачі" },
    { name: "palletHandling", title: "Палети" },
    { name: "animals", title: "Тварини" },
    { name: "woodHarvesting", title: "Лісозаготівля" },
    { name: "placeables", title: "Будівлі" },
    { name: "misc", title: "Різне" },
  ];

  function siteUrl(cfg) {
    const u = (cfg.SITE_URL || `https://${cfg.OWNER}.github.io/${cfg.REPO}`).replace(/\/+$/, "");
    return u;
  }

  // Значення catalog.data гра читає шаблоном [^%c]* (без керуючих символів).
  // Переноси рядків пишемо як літеральне \n (клієнт перетворює назад).
  function cleanValue(v) {
    return String(v == null ? "" : v)
      .replace(/\r?\n/g, "\\n")
      .replace(/[\u0000-\u001f\u007f]/g, " ")
      .replace(/count=/gi, "count :")
      .trim();
  }

  const encPath = (p) => String(p).split("/").map(encodeURIComponent).join("/");

  function buildCatalog(mods, cfg) {
    const base = siteUrl(cfg);
    const L = ["count=" + mods.length];
    mods.forEach((m, i) => {
      const p = "mod" + i + "_";
      L.push(p + "title=" + cleanValue(m.title));
      L.push(p + "author=" + cleanValue(m.author));
      L.push(p + "version=" + cleanValue(m.version));
      L.push(p + "category=" + cleanValue(m.category));
      L.push(p + "filename=" + cleanValue(m.filename));
      L.push(p + "sha256=" + (m.sha256 || ""));
      L.push(p + "size=" + (m.size || 0));
      L.push(p + "downloadUrl=" + (m.downloadUrl || ""));
      L.push(p + "imageUrl=" + (m.image ? base + "/" + encPath(m.image) : ""));
      L.push(p + "description=" + cleanValue(m.description));
      for (let s = 0; s < 4; s++) {
        const img = (m.screenshots || [])[s];
        L.push(p + "screenshot" + (s + 1) + "Url=" + (img ? base + "/" + encPath(img) : ""));
      }
    });
    return L.join("\n") + "\n";
  }

  // ---- потоковий SHA-256 (для великих файлів, без завантаження в пам'ять цілком) ----
  const primes = [];
  for (let n = 2; primes.length < 64; n++) {
    if (primes.every((p) => n % p)) primes.push(n);
  }
  const frac32 = (x) => Math.floor((x - Math.floor(x)) * 4294967296) >>> 0;
  const K = new Uint32Array(primes.map((p) => frac32(Math.cbrt(p))));
  const H0 = new Uint32Array(primes.slice(0, 8).map((p) => frac32(Math.sqrt(p))));

  class Sha256 {
    constructor() {
      this.h = new Uint32Array(H0);
      this.buf = new Uint8Array(64);
      this.fill = 0;
      this.total = 0;
      this.w = new Uint32Array(64);
    }
    _block(b, o) {
      const w = this.w, h = this.h;
      for (let i = 0; i < 16; i++) {
        w[i] = (b[o + 4 * i] << 24) | (b[o + 4 * i + 1] << 16) | (b[o + 4 * i + 2] << 8) | b[o + 4 * i + 3];
      }
      for (let i = 16; i < 64; i++) {
        const x = w[i - 15], y = w[i - 2];
        const s0 = ((x >>> 7) | (x << 25)) ^ ((x >>> 18) | (x << 14)) ^ (x >>> 3);
        const s1 = ((y >>> 17) | (y << 15)) ^ ((y >>> 19) | (y << 13)) ^ (y >>> 10);
        w[i] = (w[i - 16] + s0 + w[i - 7] + s1) | 0;
      }
      let a = h[0], b2 = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
      for (let i = 0; i < 64; i++) {
        const S1 = ((e >>> 6) | (e << 26)) ^ ((e >>> 11) | (e << 21)) ^ ((e >>> 25) | (e << 7));
        const ch = (e & f) ^ (~e & g);
        const t1 = (hh + S1 + ch + K[i] + w[i]) | 0;
        const S0 = ((a >>> 2) | (a << 30)) ^ ((a >>> 13) | (a << 19)) ^ ((a >>> 22) | (a << 10));
        const maj = (a & b2) ^ (a & c) ^ (b2 & c);
        const t2 = (S0 + maj) | 0;
        hh = g; g = f; f = e; e = (d + t1) | 0; d = c; c = b2; b2 = a; a = (t1 + t2) | 0;
      }
      h[0] = (h[0] + a) | 0; h[1] = (h[1] + b2) | 0; h[2] = (h[2] + c) | 0; h[3] = (h[3] + d) | 0;
      h[4] = (h[4] + e) | 0; h[5] = (h[5] + f) | 0; h[6] = (h[6] + g) | 0; h[7] = (h[7] + hh) | 0;
    }
    update(data) {
      let i = 0;
      this.total += data.length;
      if (this.fill) {
        const need = 64 - this.fill;
        const take = Math.min(need, data.length);
        this.buf.set(data.subarray(0, take), this.fill);
        this.fill += take; i = take;
        if (this.fill === 64) { this._block(this.buf, 0); this.fill = 0; }
      }
      for (; i + 64 <= data.length; i += 64) this._block(data, i);
      if (i < data.length) { this.buf.set(data.subarray(i), 0); this.fill = data.length - i; }
    }
    hex() {
      const bits = this.total * 8;
      const pad = new Uint8Array(((this.fill < 56 ? 56 : 120) - this.fill) + 8);
      pad[0] = 0x80;
      const hi = Math.floor(bits / 4294967296), lo = bits >>> 0;
      const n = pad.length;
      pad[n - 8] = hi >>> 24; pad[n - 7] = hi >>> 16; pad[n - 6] = hi >>> 8; pad[n - 5] = hi;
      pad[n - 4] = lo >>> 24; pad[n - 3] = lo >>> 16; pad[n - 2] = lo >>> 8; pad[n - 1] = lo;
      const saved = this.total;
      this.update(pad);
      this.total = saved;
      return Array.from(this.h, (x) => (x >>> 0).toString(16).padStart(8, "0")).join("");
    }
  }

  // Читає File/Blob шматками по 4 МБ і повертає hex SHA-256.
  async function sha256File(file, onProgress) {
    const s = new Sha256();
    const CH = 4 * 1024 * 1024;
    for (let off = 0; off < file.size; off += CH) {
      const buf = new Uint8Array(await file.slice(off, off + CH).arrayBuffer());
      s.update(buf);
      if (onProgress) onProgress(Math.min(100, ((off + buf.length) / file.size) * 100));
    }
    return s.hex();
  }

  root.FS = { CATEGORIES, siteUrl, cleanValue, buildCatalog, Sha256, sha256File };
  if (typeof module !== "undefined") module.exports = root.FS;
})(typeof window !== "undefined" ? window : globalThis);
