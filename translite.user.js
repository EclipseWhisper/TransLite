// ==UserScript==
// @name         微软自动翻译
// @namespace    microsoft-auto-zh-hans-inline
// @version      1.7.6
// @description  基于 Microsoft Translator 的轻量网页自动翻译脚本，自动将网页内容翻译为简体中文。
// @license      MIT
// @homepageURL  https://github.com/EclipseWhisper/TransLite
// @supportURL   https://github.com/EclipseWhisper/TransLite/issues
// @updateURL    https://raw.githubusercontent.com/EclipseWhisper/TransLite/main/translite.user.js
// @downloadURL  https://raw.githubusercontent.com/EclipseWhisper/TransLite/main/translite.user.js
// @match        *://*/*
// @connect      edge.microsoft.com
// @connect      api-edge.cognitive.microsofttranslator.com
// @grant        GM_xmlhttpRequest
// @grant        GM.xmlHttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM.getValue
// @grant        GM.setValue
// @run-at       document-start
// ==/UserScript==

(function () {
  var AUTH = 'https://edge.microsoft.com/translate/auth';
  var API = 'https://api-edge.cognitive.microsofttranslator.com/translate?api-version=3.0&to=zh-Hans&textType=plain&includeSentenceLength=true';
  var API_HTML = 'https://api-edge.cognitive.microsofttranslator.com/translate?api-version=3.0&to=zh-Hans&textType=html&includeSentenceLength=true';

  var VIEW_MARGIN = 2600;
  var MAX_UNITS = 420;
  var MAX_CHARS = 42000;
  var CHUNK_NODES = 25;
  var CHUNK_CHARS = 4800;
  var CONCURRENCY = 6;
  var DELAY = 70;
  var CACHE_LIMIT = 1500;

  var token = '';
  var tokenTime = 0;
  var running = false;
  var pending = false;
  var enabled = true;
  var dragMoved = false;
  var timer = 0;
  var mutedUntil = 0;
  var btn, tip, btnCanvas;
  var cache = {};
  var cacheKeys = [];
  var failedTexts = {};
  var retryFailedOnce = false;
  var markNode = typeof WeakMap !== 'undefined' ? new WeakMap() : null;
  var markEl = typeof WeakMap !== 'undefined' ? new WeakMap() : null;
  var originNode = typeof WeakMap !== 'undefined' ? new WeakMap() : null;
  var originEl = typeof WeakMap !== 'undefined' ? new WeakMap() : null;
  var originAttr = typeof WeakMap !== 'undefined' ? new WeakMap() : null;
  var markAttr = typeof WeakMap !== 'undefined' ? new WeakMap() : null;
  var originNodes = [];
  var originEls = [];
  var originAttrEls = [];
  var originTitle = '';
  var POS_KEY = 'ms_auto_zh_btn_pos';
  var EDGE_VISIBLE = 48;
  var SET_PREFIX = 'ms_auto_zh_';
  var ALWAYS_HOSTS_KEY = SET_PREFIX + 'always_hosts';
  var HOST = normalizeHost(location.hostname);
  var SITE_KEY = SET_PREFIX + 'site_' + HOST;
  var menu;
  var siteMode = settingGet(SITE_KEY, 'auto');
  var userAlwaysHosts = loadHostList(ALWAYS_HOSTS_KEY);
  var skipChinesePage = true;
  enabled = siteMode !== 'skip';


  function req(o, ok, bad) {
    o.timeout = o.timeout || 16000;

    if (typeof GM_xmlhttpRequest === 'function') {
      o.onload = ok;
      o.onerror = function () { bad('\u8bf7\u6c42\u5931\u8d25'); };
      o.ontimeout = function () { bad('\u8bf7\u6c42\u8d85\u65f6'); };
      GM_xmlhttpRequest(o);
      return;
    }

    if (typeof GM !== 'undefined' && GM.xmlHttpRequest) {
      GM.xmlHttpRequest(o).then(ok).catch(function (e) {
        bad(String(e && e.message ? e.message : e));
      });
      return;
    }

    fetch(o.url, {
      method: o.method || 'GET',
      headers: o.headers || {},
      body: o.data
    }).then(function (r) {
      return r.text().then(function (x) {
        ok({ status: r.status, responseText: x });
      });
    }).catch(function (e) {
      bad(String(e && e.message ? e.message : e));
    });
  }

  function storeGet(k, cb) {
    try {
      if (typeof GM_getValue === 'function') {
        cb(GM_getValue(k, ''));
        return;
      }

      if (typeof GM !== 'undefined' && GM.getValue) {
        GM.getValue(k, '').then(function (v) {
          cb(v || '');
        }).catch(function () {
          cb('');
        });
        return;
      }

      cb(localStorage.getItem(k) || '');
      return;
    } catch (e) {
      cb('');
    }
  }

  function storeSet(k, v) {
    try {
      if (typeof GM_setValue === 'function') {
        GM_setValue(k, v);
        return;
      }

      if (typeof GM !== 'undefined' && GM.setValue) {
        GM.setValue(k, v);
        return;
      }

      localStorage.setItem(k, v);
    } catch (e) {}
  }

  function restoreButtonPosition() {
    storeGet(POS_KEY, function (v) {
      if (!btn || !btn.parentNode) return;

      var p;

      try {
        p = JSON.parse(v || '');
      } catch (e) {
        p = null;
      }

      var r = btn.getBoundingClientRect();
      var w = r.width || 48;
      var h = r.height || 48;
      var minLeft = -(w - EDGE_VISIBLE);
      var maxLeft = Math.max(0, innerWidth - EDGE_VISIBLE);
      var left;
      var top;
      var dockLeft;

      if (p && typeof p.left === 'number' && typeof p.top === 'number') {
        dockLeft = p.left + w / 2 < innerWidth / 2;
        left = dockLeft ? minLeft : maxLeft;
        top = Math.max(4, Math.min(innerHeight - h - 4, p.top));
      } else {
        dockLeft = false;
        left = maxLeft;
        top = Math.max(4, Math.min(innerHeight - h - 4, innerHeight * 0.62));
      }

      btn.style.left = left + 'px';
      btn.style.top = top + 'px';
      btn.style.right = 'auto';
      btn.style.bottom = 'auto';
      setDockSide(dockLeft ? 'left' : 'right');
      saveButtonPosition();
    });
  }

  function saveButtonPosition() {
    if (!btn) return;
    var r = btn.getBoundingClientRect();
    storeSet(POS_KEY, JSON.stringify({ left: r.left, top: r.top }));
  }

  function setDockSide(side) {
    if (!btn) return;

    btn.classList.toggle('ms-auto-zh-dock-left', side === 'left');
    btn.classList.toggle('ms-auto-zh-dock-right', side === 'right');
  }

  function snapButtonToEdge() {
    if (!btn) return;

    var r = btn.getBoundingClientRect();
    var w = r.width || 48;
    var h = r.height || 48;
    var top = Math.max(4, Math.min(innerHeight - h - 4, r.top));
    var left;

    if (r.left + r.width / 2 < innerWidth / 2) {
      left = -(w - EDGE_VISIBLE);
      setDockSide('left');
    } else {
      left = Math.max(0, innerWidth - EDGE_VISIBLE);
      setDockSide('right');
    }

    btn.style.left = left + 'px';
    btn.style.top = top + 'px';
    btn.style.right = 'auto';
    btn.style.bottom = 'auto';
    saveButtonPosition();
  }

  function settingGet(k, d) {
    try {
      var v;

      if (typeof GM_getValue === 'function') {
        v = GM_getValue(k, null);
        return v === null || v === undefined || v === '' ? d : v;
      }

      v = localStorage.getItem(k);
      return v === null ? d : v;
    } catch (e) {
      return d;
    }
  }

  function settingSet(k, v) {
    try {
      if (typeof GM_setValue === 'function') {
        GM_setValue(k, v);
        return;
      }

      localStorage.setItem(k, v);
    } catch (e) {}
  }

  function normalizeHost(h) {
    return String(h || '').replace(/^\.+|\.+$/g, '').toLowerCase();
  }

  function loadHostList(k) {
    var raw = settingGet(k, '[]');
    var list;

    try {
      list = JSON.parse(raw || '[]');
    } catch (e) {
      list = [];
    }

    if (!Array.isArray(list)) list = [];

    var out = [];
    for (var i = 0; i < list.length; i++) {
      var h = normalizeHost(list[i]);
      if (h && out.indexOf(h) < 0) out.push(h);
    }

    return out;
  }

  function saveHostList(k, list) {
    try {
      settingSet(k, JSON.stringify(list || []));
    } catch (e) {}
  }

  function hostInList(host, list) {
    host = normalizeHost(host);

    for (var i = 0; i < list.length; i++) {
      var rule = normalizeHost(list[i]);
      if (host === rule || host.slice(-rule.length - 1) === '.' + rule) return true;
    }

    return false;
  }

  function addAlwaysHost(host) {
    host = normalizeHost(host);
    if (!host || hostInList(host, userAlwaysHosts)) return;
    userAlwaysHosts.push(host);
    saveHostList(ALWAYS_HOSTS_KEY, userAlwaysHosts);
  }

  function removeAlwaysHost(host) {
    host = normalizeHost(host);
    var next = [];

    for (var i = 0; i < userAlwaysHosts.length; i++) {
      var rule = normalizeHost(userAlwaysHosts[i]);
      if (rule && rule !== host) next.push(rule);
    }

    userAlwaysHosts = next;
    saveHostList(ALWAYS_HOSTS_KEY, userAlwaysHosts);
  }

  function siteSkipped() {
    return siteMode === 'skip';
  }

  function forceAlwaysHost() {
    return hostInList(HOST, userAlwaysHosts);
  }

  function siteAlways() {
    return siteMode === 'always' || (siteMode === 'auto' && forceAlwaysHost());
  }

  function setSiteMode(v) {
    siteMode = v === 'skip' || v === 'always' ? v : 'auto';

    if (siteMode === 'always') {
      addAlwaysHost(HOST);
    } else if (siteMode === 'auto') {
      removeAlwaysHost(HOST);
    }

    settingSet(SITE_KEY, siteMode);
  }

  function getToken(cb) {
    if (token && Date.now() - tokenTime < 8 * 60 * 1000) {
      cb('');
      return;
    }

    req({ method: 'GET', url: AUTH }, function (r) {
      var t = String(r.responseText || '').trim();

      if (r.status < 200 || r.status >= 300 || !t) {
        cb('\u83b7\u53d6\u4ee4\u724c\u5931\u8d25');
        return;
      }

      token = t;
      tokenTime = Date.now();
      cb('');
    }, cb);
  }

  var SPACE_FIX_RANGES = [
    [[0x0370, 0x03ff], [0x1f00, 0x1fff]],
    [[0x0400, 0x052f], [0x2de0, 0x2dff], [0xa640, 0xa69f]],
    [[0x0530, 0x058f]],
    [[0x0590, 0x05ff]],
    [[0x0600, 0x06ff], [0x0700, 0x077f], [0x08a0, 0x08ff]],
    [[0x0900, 0x0dff]],
    [[0x0e00, 0x0eff]],
    [[0x1000, 0x109f]],
    [[0x10a0, 0x10ff]],
    [[0x1200, 0x137f]],
    [[0x1780, 0x17ff]],
    [[0xac00, 0xd7af]]
  ];

  function hex4(n) {
    return ('0000' + n.toString(16)).slice(-4);
  }

  function rangeClass(ranges) {
    var s = '[';

    for (var i = 0; i < ranges.length; i++) {
      s += '\\u' + hex4(ranges[i][0]) + '-\\u' + hex4(ranges[i][1]);
    }

    return s + ']';
  }

  function repairSpacedLettersByClass(s, cls, keepAcronym) {
    var re = new RegExp('(?:' + cls + '[ \\t\\u00A0]+){3,}' + cls, 'g');

    return String(s || '').replace(re, function (m) {
      var joined = m.replace(/[ \t\u00A0]+/g, '');

      if (joined.length < 4) return m;

      if (keepAcronym) {
        if (/^[A-Z]{2,8}$/.test(joined)) return m;
        if (/^(?:API|URL|URI|HTTP|HTTPS|HTML|CSS|XML|JSON|SQL|VPN|CPU|GPU|RAM|ROM|USB|DNS|TCP|UDP|SSH|SSL|TLS|APK|SDK|NDK|JDK|UI|UX)$/i.test(joined)) return m;
      }

      return m.replace(new RegExp('(' + cls + ')([ \\t\\u00A0]+)(?=' + cls + ')', 'g'), function (_, ch, sp) {
        return ch + (sp.length >= 2 ? ' ' : '');
      });
    });
  }

  function normalizeTranslateInput(t) {
    var s = String(t || '');

    for (var i = 0; i < SPACE_FIX_RANGES.length; i++) {
      s = repairSpacedLettersByClass(s, rangeClass(SPACE_FIX_RANGES[i]), false);
    }

    return repairSpacedLettersByClass(s, '[A-Za-z]', true);
  }

  function setCache(src, dst) {
    if (!src || !dst || cache[src]) return;

    cache[src] = cleanup(dst);
    cacheKeys.push(src);

    if (cacheKeys.length > CACHE_LIMIT) {
      delete cache[cacheKeys.shift()];
    }
  }

  function markFailed(arr) {
    for (var i = 0; i < arr.length; i++) {
      if (arr[i]) failedTexts[arr[i]] = 1;
    }
  }

  function clearFailed(t) {
    if (t && failedTexts[t]) {
      delete failedTexts[t];
    }
  }

  function failedCount() {
    var n = 0;

    for (var k in failedTexts) {
      if (failedTexts[k]) n++;
    }

    return n;
  }

  function cleanup(s) {
    s = String(s || '').trim();
    s = s.replace(/([\u4e00-\u9fff])\s+(?=[\u4e00-\u9fff])/g, '$1');
    s = s.replace(/\s+([，。！？：；、）】》])/g, '$1');
    s = s.replace(/([（【《])\s+/g, '$1');
    s = s.replace(/([\u4e00-\u9fff])\s+([，。！？：；、])/g, '$1$2');
    return s;
  }

  var HTML_PREFIX = '__MS_AUTO_ZH_HTML__';

  function htmlKey(s) {
    return HTML_PREFIX + String(s || '');
  }

  function isHtmlKey(s) {
    return String(s || '').indexOf(HTML_PREFIX) === 0;
  }

  function stripHtmlKey(s) {
    s = String(s || '');
    return isHtmlKey(s) ? s.slice(HTML_PREFIX.length) : s;
  }

  function modeOfText(s) {
    return isHtmlKey(s) ? 'html' : 'plain';
  }

  function rememberNode(node, raw) {
    if (!originNode || originNode.has(node)) return;

    originNode.set(node, raw);
    originNodes.push(node);
  }

  function rememberEl(el) {
    if (!originEl || originEl.has(el)) return;

    originEl.set(el, el.innerHTML);
    originEls.push(el);
  }

  function rememberAttr(el, key, raw) {
    if (!originAttr || !el) return;

    var rec = originAttr.get(el);
    if (!rec) {
      rec = {};
      originAttr.set(el, rec);
      originAttrEls.push(el);
    }

    if (!(key in rec)) {
      rec[key] = raw;
    }
  }

  function writeAttr(el, key, dst) {
    if (!el || !key) return false;

    var raw = key === 'value' ? String(el.value || el.getAttribute(key) || '') : String(el.getAttribute(key) || '');
    if (!raw || raw === dst) return false;

    rememberAttr(el, key, raw);

    if (key === 'value') {
      try { el.value = dst; } catch (e) {}
      el.setAttribute(key, dst);
    } else {
      el.setAttribute(key, dst);
    }

    if (markAttr) {
      var rec = markAttr.get(el) || {};
      rec[key] = dst;
      markAttr.set(el, rec);
    }

    return true;
  }

  function writeUnit(unit, dst) {
    if (!unit) return;

    mutedUntil = Date.now() + 160;
    dst = cleanup(dst);

    if (unit.type === 'html') {
      if (!unit.el || !unit.el.isConnected) return;

      rememberEl(unit.el);
      unit.el.innerHTML = dst;
      unit.el.setAttribute('data-ms-translated-unit', '1');

      if (markEl) {
        markEl.set(unit.el, unit.el.textContent.trim());
      }

      return;
    }

    if (unit.type === 'el') {
      if (!unit.el || !unit.el.isConnected) return;

      rememberEl(unit.el);
      unit.el.textContent = dst;
      unit.el.setAttribute('data-ms-translated-unit', '1');

      if (markEl) {
        markEl.set(unit.el, dst);
      }

      return;
    }

    if (!unit.node || !unit.node.parentNode) return;

    rememberNode(unit.node, unit.raw);
    unit.node.nodeValue = unit.head + dst + unit.tail;

    if (markNode) {
      markNode.set(unit.node, dst);
    }
  }

  function restoreOriginal() {
    if (originTitle) {
      document.title = originTitle;
      originTitle = '';
    }

    for (var i = 0; i < originEls.length; i++) {
      var e = originEls[i];

      if (e && e.parentNode && originEl && originEl.has(e)) {
        e.innerHTML = originEl.get(e);
        e.removeAttribute('data-ms-translated-unit');
      }
    }

    for (var j = 0; j < originNodes.length; j++) {
      var n = originNodes[j];

      if (n && n.parentNode && originNode && originNode.has(n)) {
        n.nodeValue = originNode.get(n);
      }
    }

    for (var k = 0; k < originAttrEls.length; k++) {
      var a = originAttrEls[k];
      var rec = a && originAttr && originAttr.get(a);

      if (!a || !rec) continue;

      for (var key in rec) {
        if (key === 'value') {
          try { a.value = rec[key]; } catch (e) {}
          a.setAttribute(key, rec[key]);
        } else {
          a.setAttribute(key, rec[key]);
        }
      }
    }

    originNode = typeof WeakMap !== 'undefined' ? new WeakMap() : null;
    originEl = typeof WeakMap !== 'undefined' ? new WeakMap() : null;
    originAttr = typeof WeakMap !== 'undefined' ? new WeakMap() : null;
    originNodes = [];
    originEls = [];
    originAttrEls = [];
    markNode = typeof WeakMap !== 'undefined' ? new WeakMap() : null;
    markEl = typeof WeakMap !== 'undefined' ? new WeakMap() : null;
    markAttr = typeof WeakMap !== 'undefined' ? new WeakMap() : null;
  }

  function ensureUiStyle() {
    if (document.getElementById('ms-auto-zh-ui-style')) return;

    var s = document.createElement('style');
    s.id = 'ms-auto-zh-ui-style';
    s.textContent =
      '#ms-auto-zh-btn,#ms-auto-zh-menu,#ms-auto-zh-tip{font-family:MiSans,"MiSans VF","Xiaomi Sans",system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif!important;-webkit-tap-highlight-color:transparent!important;}' +

      '#ms-auto-zh-btn{' +
        'position:fixed!important;z-index:2147483646!important;width:48px!important;height:48px!important;margin:0!important;padding:0!important;border:0!important;border-radius:0!important;' +
        'background:transparent!important;box-sizing:border-box!important;display:flex!important;align-items:center!important;justify-content:center!important;overflow:visible!important;opacity:1!important;' +
        'touch-action:none!important;user-select:none!important;-webkit-user-select:none!important;-webkit-appearance:none!important;appearance:none!important;cursor:pointer!important;' +
      '}' +
      '#ms-auto-zh-btn.ms-auto-zh-dock-left{justify-content:flex-start!important;}' +
      '#ms-auto-zh-btn.ms-auto-zh-dock-right{justify-content:flex-end!important;}' +
      '#ms-auto-zh-btn-core{' +
        'position:relative!important;width:36px!important;height:36px!important;border-radius:15px!important;display:flex!important;align-items:center!important;justify-content:center!important;overflow:hidden!important;opacity:1!important;' +
        'background:linear-gradient(180deg,rgba(255,255,255,.99),rgba(247,248,251,.98))!important;border:1px solid rgba(255,255,255,.98)!important;' +
        'box-shadow:0 9px 22px rgba(30,36,50,.14),0 3px 7px rgba(30,36,50,.075),inset 0 1px 0 rgba(255,255,255,1)!important;' +
        'backdrop-filter:blur(28px) saturate(180%) brightness(1.03)!important;-webkit-backdrop-filter:blur(28px) saturate(180%) brightness(1.03)!important;pointer-events:none!important;' +
        'transition:transform .18s cubic-bezier(.2,.8,.2,1),box-shadow .18s ease,background .18s ease!important;' +
      '}' +
      '#ms-auto-zh-btn-core:before{content:""!important;position:absolute!important;inset:0!important;border-radius:inherit!important;background:linear-gradient(180deg,rgba(255,255,255,.72),rgba(255,255,255,0) 58%)!important;pointer-events:none!important;}' +
      '#ms-auto-zh-btn-core:after{content:""!important;position:absolute!important;inset:1px!important;border-radius:14px!important;border:1px solid rgba(255,255,255,.7)!important;pointer-events:none!important;}' +
      '#ms-auto-zh-btn.ms-auto-zh-dock-left #ms-auto-zh-btn-core{transform:translateX(-9px)!important;}' +
      '#ms-auto-zh-btn.ms-auto-zh-dock-right #ms-auto-zh-btn-core{transform:translateX(9px)!important;}' +
      '#ms-auto-zh-btn.ms-auto-zh-dragging #ms-auto-zh-btn-core{transform:translateX(0) scale(1.06)!important;}' +
      '#ms-auto-zh-btn.ms-auto-zh-off #ms-auto-zh-btn-core{background:linear-gradient(180deg,rgba(255,255,255,.99),rgba(247,248,251,.98))!important;box-shadow:0 9px 22px rgba(30,36,50,.14),0 3px 7px rgba(30,36,50,.075),inset 0 1px 0 rgba(255,255,255,1)!important;}' +
      '#ms-auto-zh-btn-text{' +
        'position:relative!important;z-index:1!important;display:block!important;width:36px!important;height:36px!important;color:#050505!important;text-align:center!important;text-shadow:none!important;' +
        'font:950 13px/36px MiSans,"MiSans VF","Xiaomi Sans",system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif!important;pointer-events:none!important;letter-spacing:-.02em!important;' +
      '}' +
      '#ms-auto-zh-tip{' +
        'position:fixed!important;left:50%!important;bottom:24px!important;transform:translateX(-50%)!important;z-index:2147483647!important;display:none!important;max-width:82vw!important;' +
        'padding:8px 13px!important;border-radius:18px!important;background:rgba(255,255,255,.86)!important;border:1px solid rgba(255,255,255,.92)!important;' +
        'backdrop-filter:blur(28px) saturate(180%)!important;-webkit-backdrop-filter:blur(28px) saturate(180%)!important;box-shadow:0 14px 34px rgba(33,39,54,.14)!important;' +
        'color:#2f3136!important;font:650 12px/1.35 MiSans,"MiSans VF","Xiaomi Sans",system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif!important;text-align:center!important;' +
      '}' +
      '#ms-auto-zh-tip.ms-show{display:block!important;}' +

      '#ms-auto-zh-menu{' +
        'position:fixed!important;z-index:2147483647!important;width:218px!important;max-width:calc(100vw - 12px)!important;padding:6px!important;border-radius:23px!important;' +
        'background:linear-gradient(180deg,rgba(248,248,250,.96),rgba(241,242,246,.92))!important;border:1px solid rgba(255,255,255,.9)!important;' +
        'backdrop-filter:blur(46px) saturate(190%) brightness(1.04)!important;-webkit-backdrop-filter:blur(46px) saturate(190%) brightness(1.04)!important;' +
        'box-shadow:0 16px 40px rgba(26,32,46,.15),0 5px 13px rgba(26,32,46,.07),inset 0 1px 0 rgba(255,255,255,.92)!important;color:#050505!important;box-sizing:border-box!important;' +
        'user-select:none!important;-webkit-user-select:none!important;pointer-events:auto!important;overflow:hidden!important;' +
      '}' +
      '#ms-auto-zh-menu:not(.ms-show){display:none!important;}' +
      '#ms-auto-zh-menu.ms-show{display:block!important;}' +
      '#ms-auto-zh-menu *{box-sizing:border-box!important;}' +
      '.ms-auto-zh-label{padding:5px 9px 4px!important;font:900 10.5px/1 MiSans,"MiSans VF","Xiaomi Sans",system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif!important;color:#9a9ca6!important;letter-spacing:.01em!important;}' +
      '.ms-auto-zh-card{overflow:hidden!important;border-radius:19px!important;background:rgba(255,255,255,.97)!important;border:1px solid rgba(255,255,255,1)!important;box-shadow:0 6px 16px rgba(30,36,50,.045),inset 0 1px 0 rgba(255,255,255,1)!important;}' +
      '.ms-auto-zh-row{width:100%!important;min-height:40px!important;padding:5px 8px!important;border:0!important;border-radius:0!important;background:transparent!important;color:#050505!important;text-align:left!important;display:grid!important;grid-template-columns:24px minmax(0,1fr) auto!important;align-items:center!important;column-gap:7px!important;-webkit-appearance:none!important;appearance:none!important;touch-action:manipulation!important;}' +
      '.ms-auto-zh-row:active{background:rgba(0,0,0,.045)!important;}' +
      '.ms-auto-zh-row.ms-auto-zh-selected{background:rgba(55,132,245,.075)!important;}' +
      '.ms-auto-zh-card .ms-auto-zh-row+.ms-auto-zh-row{border-top:1px solid rgba(0,0,0,.04)!important;}' +
      '.ms-auto-zh-ico{width:23px!important;height:23px!important;border-radius:9px!important;display:flex!important;align-items:center!important;justify-content:center!important;background:transparent!important;color:#000!important;font:950 15px/1 MiSans,"MiSans VF","Xiaomi Sans",system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif!important;}' +
      '.ms-auto-zh-mid{min-width:0!important;}' +
      '.ms-auto-zh-name{display:block!important;color:#050505!important;font:950 13.5px/1.08 MiSans,"MiSans VF","Xiaomi Sans",system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif!important;white-space:nowrap!important;overflow:hidden!important;text-overflow:ellipsis!important;letter-spacing:-.018em!important;}' +
      '.ms-auto-zh-desc{display:block!important;margin-top:2px!important;color:#6d7078!important;font:700 10px/1.12 MiSans,"MiSans VF","Xiaomi Sans",system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif!important;white-space:nowrap!important;overflow:hidden!important;text-overflow:ellipsis!important;}' +
      '.ms-auto-zh-val{font:850 11px/1.05 MiSans,"MiSans VF","Xiaomi Sans",system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif!important;color:#92949b!important;white-space:nowrap!important;display:flex!important;align-items:center!important;gap:4px!important;}' +
      '.ms-auto-zh-val:empty{display:none!important;}' +
      '.ms-auto-zh-val.gray{color:#a2a3a8!important;}' +
      '.ms-auto-zh-chevron{width:9px!important;height:9px!important;border-right:2.5px solid #9b9da3!important;border-bottom:2.5px solid #9b9da3!important;transform:rotate(-45deg)!important;display:inline-block!important;margin-left:2px!important;}' +
      '.ms-auto-zh-switch{position:relative!important;width:36px!important;height:22px!important;border-radius:999px!important;background:#d7d9df!important;box-shadow:inset 0 1px 2px rgba(0,0,0,.07)!important;display:inline-block!important;}' +
      '.ms-auto-zh-switch:after{content:""!important;position:absolute!important;width:18px!important;height:18px!important;border-radius:50%!important;left:2px!important;top:2px!important;background:#fff!important;box-shadow:0 2px 5px rgba(0,0,0,.18)!important;transition:left .18s cubic-bezier(.2,.8,.2,1)!important;}' +
      '.ms-auto-zh-switch.on{background:#3488f6!important;}' +
      '.ms-auto-zh-switch.on:after{left:16px!important;}' +
      '.ms-auto-zh-row.ms-auto-zh-selected .ms-auto-zh-ico{color:#3488f6!important;}' +
      '.ms-auto-zh-spacer{height:6px!important;}';

    (document.head || document.documentElement).appendChild(s);
  }

  function setButtonState(label) {
    if (!btn) return;
    if (btnCanvas) btnCanvas.textContent = '译';
    btn.classList.toggle('ms-auto-zh-off', !enabled);
  }

  function setButtonLabel(t) {
    setButtonState(t);
  }

  function ui() {
    ensureUiStyle();

    btn = document.createElement('button');
    btn.id = 'ms-auto-zh-btn';
    btn.setAttribute('data-ms-translator', '1');
    btn.setAttribute('aria-label', '微软自动翻译');

    var core = document.createElement('span');
    core.id = 'ms-auto-zh-btn-core';
    core.setAttribute('aria-hidden', 'true');

    btnCanvas = document.createElement('span');
    btnCanvas.id = 'ms-auto-zh-btn-text';
    btnCanvas.setAttribute('aria-hidden', 'true');
    core.appendChild(btnCanvas);
    btn.appendChild(core);

    setButtonState('译');

    btn.oncontextmenu = function (e) {
      e.preventDefault();
      e.stopPropagation();
      return false;
    };

    document.documentElement.appendChild(btn);
    restoreButtonPosition();
    drag(btn);

    tip = document.createElement('div');
    tip.id = 'ms-auto-zh-tip';
    tip.setAttribute('data-ms-translator', '1');
    document.documentElement.appendChild(tip);
  }

  function hideMenu() {
    if (menu) {
      menu.classList.remove('ms-show');
    }
  }

  function isMenuVisible() {
    return menu && menu.classList.contains('ms-show');
  }

  function tag(name, cls, text) {
    var n = document.createElement(name);
    if (cls) n.className = cls;
    if (text !== undefined && text !== null) n.textContent = text;
    return n;
  }

  function row(icon, title, desc, value, fn, arrow) {
    var b = tag('button', 'ms-auto-zh-row');
    b.type = 'button';
    b.setAttribute('data-ms-translator', '1');

    b.appendChild(tag('span', 'ms-auto-zh-ico', icon));

    var mid = tag('span', 'ms-auto-zh-mid');
    mid.appendChild(tag('span', 'ms-auto-zh-name', title));
    if (desc) mid.appendChild(tag('span', 'ms-auto-zh-desc', desc));
    b.appendChild(mid);

    var v = tag('span', 'ms-auto-zh-val' + (value === '无' ? ' gray' : ''));
    if (value && value.nodeType) {
      v.appendChild(value);
    } else if (value !== undefined && value !== null) {
      v.textContent = String(value);
    }
    if (arrow) v.appendChild(tag('i', 'ms-auto-zh-chevron'));
    b.appendChild(v);

    b.addEventListener('click', function (e) {
      e.preventDefault();
      e.stopPropagation();
      if (fn) fn();
      renderMenu();
    }, true);

    return b;
  }

  function switchValue(on) {
    var s = tag('span', 'ms-auto-zh-switch' + (on ? ' on' : ''));
    s.setAttribute('aria-hidden', 'true');
    return s;
  }

  function modeRow(value, title, desc, active, fn) {
    var b = row(active ? '✓' : ' ', title, desc, value, fn, false);
    if (active) b.className += ' ms-auto-zh-selected';
    return b;
  }

  function card(rows) {
    var c = tag('div', 'ms-auto-zh-card');
    for (var i = 0; i < rows.length; i++) c.appendChild(rows[i]);
    return c;
  }

  function label(text) {
    return tag('div', 'ms-auto-zh-label', text);
  }

  function renderMenu() {
    if (!menu) return;

    menu.innerHTML = '';

    menu.appendChild(label('显示'));
    menu.appendChild(card([
      row('⇄', enabled ? '显示原文' : '显示译文', '切换当前页面显示', switchValue(enabled), function () {
        hideMenu();
        toggle();
      }, false),
      row('↻', '刷新翻译', '清空缓存重新处理', '执行', function () {
        hideMenu();
        cache = {};
        cacheKeys = [];
        failedTexts = {};
        pending = false;
        clearTimeout(timer);
        restoreOriginal();
        enabled = true;
        setButtonState('译');
        say('刷新翻译');
        schedule(true);
      }, false),
      row('↥', '重试失败项', '只重试失败内容', failedCount() ? String(failedCount()) : '无', function () {
        hideMenu();
        if (!failedCount()) {
          say('没有失败项');
          return;
        }
        retryFailedOnce = true;
        enabled = true;
        setButtonState('译');
        say('重试失败项');
        schedule(true);
      }, false)
    ]));

    var effectiveAlways = siteAlways();

    menu.appendChild(tag('div', 'ms-auto-zh-spacer'));
    menu.appendChild(label('站点'));
    menu.appendChild(card([
      modeRow('自动', '自动模式', '按页面内容判断', siteMode === 'auto' && !effectiveAlways, function () {
        hideMenu();
        setSiteMode('auto');
        enabled = true;
        setButtonState('译');
        say('本站恢复自动');
        if (siteAlways()) schedule(true);
      }),
      modeRow('跳过', '本站不翻译', '以后跳过当前网站', siteMode === 'skip', function () {
        hideMenu();
        setSiteMode('skip');
        enabled = false;
        pending = false;
        clearTimeout(timer);
        restoreOriginal();
        setButtonState('译');
        say('本站不翻译');
      }),
      modeRow('总是', '本站总是翻译', '强制翻译当前网站', effectiveAlways, function () {
        hideMenu();
        setSiteMode('always');
        enabled = true;
        setButtonState('译');
        say('本站总是翻译');
        schedule(true);
      })
    ]));
  }

  function showMenu() {
    ensureUiStyle();
    if (!btn) return;

    if (!menu) {
      menu = document.createElement('div');
      menu.id = 'ms-auto-zh-menu';
      menu.setAttribute('data-ms-translator', '1');
      document.documentElement.appendChild(menu);

      menu.addEventListener('pointerdown', function (e) {
        e.stopPropagation();
      }, true);

      menu.addEventListener('touchstart', function (e) {
        e.stopPropagation();
      }, { capture: true, passive: true });
    }

    renderMenu();

    var br = btn.getBoundingClientRect();
    var gap = 3;
    var pad = 6;

    menu.style.visibility = 'hidden';
    menu.style.left = '0px';
    menu.style.right = 'auto';
    menu.style.top = '0px';
    menu.style.bottom = 'auto';
    menu.classList.add('ms-show');

    var mr = menu.getBoundingClientRect();
    var w = Math.min(mr.width || 222, innerWidth - pad * 2);
    var h = Math.min(mr.height || 300, innerHeight - pad * 2);
    var left;

    if (br.left + br.width / 2 < innerWidth / 2) {
      left = br.right + gap;
    } else {
      left = br.left - w - gap;
    }

    if (left < pad || left + w > innerWidth - pad) {
      left = Math.max(pad, Math.min(innerWidth - w - pad, left));
    }

    var top = br.top + br.height / 2 - h / 2;
    top = Math.max(pad, Math.min(innerHeight - h - pad, top));

    menu.style.left = left + 'px';
    menu.style.right = 'auto';
    menu.style.top = top + 'px';
    menu.style.bottom = 'auto';
    menu.style.visibility = '';
  }

  function drag(el) {
    var down = false;
    var active = false;
    var sx = 0;
    var sy = 0;
    var sl = 0;
    var st = 0;
    var pressTimer = 0;
    var longPressed = false;

    function stop(e) {
      if (!e) return;
      e.preventDefault();
      e.stopPropagation();
      if (e.stopImmediatePropagation) e.stopImmediatePropagation();
    }

    el.addEventListener('touchstart', stop, { capture: true, passive: false });
    el.addEventListener('contextmenu', stop, true);
    el.addEventListener('selectstart', stop, true);

    el.addEventListener('pointerdown', function (e) {
      stop(e);

      down = true;
      active = false;
      dragMoved = false;
      longPressed = false;
      sx = e.clientX;
      sy = e.clientY;
      hideMenu();

      clearTimeout(pressTimer);
      pressTimer = setTimeout(function () {
        if (!down || active || dragMoved) return;

        longPressed = true;
        showMenu();

        try {
          if (navigator.vibrate) navigator.vibrate(12);
        } catch (err) {}
      }, 185);

      var r = el.getBoundingClientRect();
      sl = r.left;
      st = r.top;

      try {
        el.setPointerCapture(e.pointerId);
      } catch (err2) {}
    }, true);

    el.addEventListener('pointermove', function (e) {
      if (!down) return;

      var dx = e.clientX - sx;
      var dy = e.clientY - sy;

      if (!active && Math.sqrt(dx * dx + dy * dy) >= 24) {
        clearTimeout(pressTimer);
        active = true;
        dragMoved = true;
        el.classList.add('ms-auto-zh-dragging');
        setDockSide('');
        el.style.left = sl + 'px';
        el.style.top = st + 'px';
        el.style.right = 'auto';
        el.style.bottom = 'auto';
      }

      if (!active) return;

      stop(e);

      var r = el.getBoundingClientRect();
      el.style.left = Math.max(4, Math.min(innerWidth - r.width - 4, sl + dx)) + 'px';
      el.style.top = Math.max(4, Math.min(innerHeight - r.height - 4, st + dy)) + 'px';
    }, true);

    function finish(e, cancel) {
      if (!down) return;

      clearTimeout(pressTimer);

      if (active) {
        snapButtonToEdge();
        dragMoved = true;

        setTimeout(function () {
          dragMoved = false;
        }, 260);
      } else if (!cancel && longPressed) {
        stop(e);
      } else if (!cancel) {
        stop(e);
        toggle();
      }

      down = false;
      longPressed = false;
      active = false;
      el.classList.remove('ms-auto-zh-dragging');

      try {
        el.releasePointerCapture(e.pointerId);
      } catch (err) {}
    }

    el.addEventListener('pointerup', function (e) {
      finish(e, false);
    }, true);

    el.addEventListener('pointercancel', function (e) {
      finish(e, true);
    }, true);
  }

  function say(s) {
    tip.textContent = s;
    tip.classList.add('ms-show');
    clearTimeout(tip._t);
    tip._t = setTimeout(function () {
      tip.classList.remove('ms-show');
    }, 1100);
  }

  function toggle() {
    if (enabled) {
      enabled = false;
      pending = false;
      clearTimeout(timer);
      restoreOriginal();
      setButtonState('译');
      say('\u5df2\u663e\u793a\u539f\u6587');
      return;
    }

    enabled = true;
    setButtonState('译');
    say('\u5df2\u663e\u793a\u8bd1\u6587');
    schedule(true);
  }

  function badParent(el) {
    while (el && el !== document.body) {
      if (el.getAttribute && el.getAttribute('data-ms-translator') === '1') return true;
      if (el.getAttribute && el.getAttribute('data-ms-translated-unit') === '1') return true;

      var t = el.tagName ? el.tagName.toLowerCase() : '';
      if (/^(script|style|noscript|textarea|input|select|option|code|pre|kbd|samp|svg|canvas)$/.test(t)) return true;
      if (el.isContentEditable) return true;

      el = el.parentNode;
    }

    return false;
  }

  function rectOfNode(node) {
    var el = node && node.parentElement;
    if (!el || badParent(el)) return null;

    var s = getComputedStyle(el);
    if (!s || s.display === 'none' || s.visibility === 'hidden' || s.opacity === '0') return null;

    var range;
    var best = null;

    try {
      range = document.createRange();
      range.selectNodeContents(node);

      var rs = range.getClientRects();

      for (var i = 0; i < rs.length; i++) {
        var r = rs[i];

        if (r.bottom > -VIEW_MARGIN && r.top < innerHeight + VIEW_MARGIN && r.right > 0 && r.left < innerWidth) {
          best = r;
          break;
        }
      }
    } catch (e) {
      best = null;
    } finally {
      if (range && range.detach) {
        range.detach();
      }
    }

    return best;
  }

  function rectOfEl(el) {
    if (!el || badParent(el)) return null;

    var s = getComputedStyle(el);
    if (!s || s.display === 'none' || s.visibility === 'hidden' || s.opacity === '0') return null;

    var r = el.getBoundingClientRect();

    if (r.bottom > -VIEW_MARGIN && r.top < innerHeight + VIEW_MARGIN && r.right > 0 && r.left < innerWidth) {
      return r;
    }

    return null;
  }

  function hasUnsafeChild(el) {
    var all = el.getElementsByTagName('*');

    for (var i = 0; i < all.length; i++) {
      var t = all[i].tagName ? all[i].tagName.toLowerCase() : '';

      if (!/^(span|b|strong|i|em|u|mark|small|sub|sup|br)$/.test(t)) {
        return true;
      }
    }

    return false;
  }




  function latinCarrierLike(t) {
    var s = String(t || '').trim();
    if (!s) return false;

    var inner = s;
    var bracketed = false;
    var m = inner.match(/^[\[\(\{【（]\s*([^\]\)\}】）]{1,240})\s*[\]\)\}】）]$/);
    if (m) {
      bracketed = true;
      inner = m[1].trim();
    }

    inner = inner
      .replace(/[·・]/g, ' ')
      .replace(/[，,；;、/|]+/g, ' ')
      .replace(/\s+/g, ' ')
      .trim();

    if (!inner) return false;

    var hasLatin = /[A-Za-zÀ-ɏüÜ]/.test(inner);
    if (!hasLatin) return false;

    var hasZh = /[\u4e00-\u9fff]/.test(inner);
    var hasSentencePunct = /[.!?。！？]/.test(inner);
    var lower = inner.toLowerCase();

    if (/[āáǎàēéěèīíǐìōóǒòūúǔùǖǘǚǜüńňǹḿɑɐɒæɓʙβɔɕçðɖɗəɚɛɜɡɣɤɦɨɪʝɭɯɲŋɳøɵɸɹɻʂʃʈʊʋʌʐʑʒʔˈˌːˑㄅ-ㄩ]/i.test(inner)) return true;

    var rawTokens = inner.split(/[\s'’\-]+/).filter(Boolean);
    if (!rawTokens.length) return false;

    function plain(w) {
      return String(w || '').toLowerCase().replace(/[1-5]$/, '').replace(/ü/g, 'v');
    }

    function pinyinSyllable(w) {
      w = plain(w);
      if (!w || w.length > 8) return false;
      if (/^(a|ai|an|ang|ao|e|ei|en|eng|er|o|ou)$/.test(w)) return true;

      var initials = '(?:zh|ch|sh|[bpmfdtnlgkhjqxzcsrwy])?';
      var finals = '(?:a|ai|an|ang|ao|e|ei|en|eng|er|i|ia|ian|iang|iao|ie|in|ing|iong|iu|o|ong|ou|u|ua|uai|uan|uang|ue|ui|un|uo|v|ve)';
      return new RegExp('^' + initials + finals + '$').test(w);
    }

    function pinyinInitial(w) {
      return /^(b|p|m|f|d|t|n|l|g|k|h|j|q|x|zh|ch|sh|r|z|c|s|y|w)$/.test(plain(w));
    }

    function pinyinFinal(w) {
      return /^(a|o|e|i|u|v|ai|ei|ui|ao|ou|iu|ie|ve|er|an|en|in|un|vn|ang|eng|ing|ong|ia|ian|iang|iao|iong|ua|uai|uan|uang|uo)$/.test(plain(w));
    }

    function alphabetUnit(w) {
      return /^[a-z]$/i.test(w) || (/^[a-z]{2}$/i.test(w) && w[0].toLowerCase() === w[1].toLowerCase());
    }

    var tokens = rawTokens.map(function (x) {
      return x.replace(/^[^A-Za-zÀ-ɏüÜ0-9]+|[^A-Za-zÀ-ɏüÜ0-9]+$/g, '');
    }).filter(Boolean);

    if (!tokens.length) return false;

    var digitTone = 0;
    var py = 0;
    var initials = 0;
    var finals = 0;
    var alpha = 0;
    var shortTokens = 0;
    var lowerTokens = 0;

    for (var i = 0; i < tokens.length; i++) {
      var w = tokens[i];
      if (/^[a-züv]{1,8}[1-5]$/i.test(w)) digitTone++;
      if (pinyinSyllable(w)) py++;
      if (pinyinInitial(w)) initials++;
      if (pinyinFinal(w)) finals++;
      if (alphabetUnit(w)) alpha++;
      if (/^[a-züv]{1,8}$/i.test(w)) shortTokens++;
      if (w === w.toLowerCase()) lowerTokens++;
    }

    if (digitTone >= 1 && digitTone === tokens.length) return true;
    if (tokens.length >= 2 && (initials === tokens.length || finals === tokens.length || py === tokens.length)) return true;
    if (!hasZh && !hasSentencePunct && tokens.length >= 2 && py >= Math.ceil(tokens.length * 0.75) && shortTokens === tokens.length && lowerTokens === tokens.length) return true;
    if (bracketed && tokens.length >= 1 && (py >= Math.ceil(tokens.length * 0.5) || initials + finals >= Math.ceil(tokens.length * 0.7))) return true;
    if (tokens.length >= 3 && alpha === tokens.length) return true;
    if (/^(?:[A-Z]\s+[a-z]\s*){2,}$/.test(inner + ' ')) return true;
    if (/^(?:[A-Z][a-z]\s*){3,}$/.test(inner.replace(/\s+/g, ' ') + ' ')) return true;
    if (!hasZh && tokens.length >= 2 && lower === inner && (py + initials + finals) >= Math.ceil(tokens.length * 0.85)) return true;

    return false;
  }

  function phoneticLike(t) {
    return latinCarrierLike(t);
  }

  function protect(t) {
    var s = String(t || '').trim();

    if (!s) return true;
    if (phoneticLike(s)) return true;
    if (/\.(apk|apks|xapk|zip|7z|rar|tar|gz|tgz|xz|img|iso|json|xml|yaml|yml|txt|md|dex|jar|so|ko|bin|exe|dll|rs|c|cpp|h|java|kt|py|js|ts|css|html)$/i.test(s)) return true;
    if (/^https?:\/\//i.test(s)) return true;
    if (/^[A-Za-z0-9._+@#:/\\()\[\]-]+$/.test(s) && /[._@#:/\\()[\]-]/.test(s)) return true;
    if (/^[a-f0-9]{7,40}$/i.test(s)) return true;
    if (/^v?\d+(\.\d+){1,4}([-+][A-Za-z0-9._-]+)?$/i.test(s)) return true;
    if (/^[A-Z0-9_]{2,12}$/.test(s)) return true;
    if (/^[A-Z][a-z]{1,3}$/.test(s)) return true;
    if (/^[A-Za-z]+[A-Z][A-Za-z0-9_.$-]*$/.test(s)) return true;
    var methodCalls = s.match(/\b[A-Za-z_$][A-Za-z0-9_$]*\s*\(\s*\)/g) || [];
    if (methodCalls.length >= 2) return true;

    var ids = s.match(/\b[A-Za-z_$][A-Za-z0-9_$]*(?:\.[A-Za-z_$][A-Za-z0-9_$]*)*\b/g) || [];
    var codeIds = 0;

    for (var i = 0; i < ids.length; i++) {
      if (/[a-z][A-Z]|[_$]/.test(ids[i]) || /^[A-Z][A-Za-z0-9_$]*[A-Z][A-Za-z0-9_$]*$/.test(ids[i])) {
        codeIds++;
      }
    }

    if (methodCalls.length >= 1 && codeIds >= 1) return true;
    if (codeIds >= 3 && /[,:;()]/.test(s)) return true;

    return false;
  }

  var RE_CJK = /[㐀-\u9fff豈-﫿]/;
  var RE_LATIN = /[A-Za-zÀ-ɏᴀ-ᵿḀ-ỿ]/;
  var RE_LETTER_FALLBACK = /[A-Za-zÀ-ɏͰ-ϿЀ-ԯ԰-֏֐-׿؀-ۿऀ-෿฀-໿က-႟Ⴀ-ჿሀ-፿ក-៿぀-ヿ가-힯]/;
  var unicodeLetterRE = null;

  function getUnicodeLetterRE() {
    if (unicodeLetterRE === false) return null;
    if (unicodeLetterRE) {
      unicodeLetterRE.lastIndex = 0;
      return unicodeLetterRE;
    }

    try {
      unicodeLetterRE = new RegExp('\\p{L}', 'gu');
      return unicodeLetterRE;
    } catch (e) {
      unicodeLetterRE = false;
      return null;
    }
  }

  function countLetters(t, nonLatinOnly) {
    var s = String(t || '');
    if (!s) return 0;

    var re = getUnicodeLetterRE();
    var n = 0;
    var i;
    var ch;

    if (re) {
      var m;
      while ((m = re.exec(s))) {
        ch = m[0];
        if (RE_CJK.test(ch)) continue;
        if (nonLatinOnly && RE_LATIN.test(ch)) continue;
        n++;
      }

      return n;
    }

    for (i = 0; i < s.length; i++) {
      ch = s.charAt(i);
      if (RE_CJK.test(ch)) continue;
      if (nonLatinOnly && RE_LATIN.test(ch)) continue;
      if (RE_LETTER_FALLBACK.test(ch)) n++;
    }

    return n;
  }

  function hasWorldLanguageLetter(t) {
    return countLetters(t, false) > 0;
  }

  function countWorldLanguageLetters(t) {
    return countLetters(t, false);
  }

  function countNonLatinForeignLetters(t) {
    return countLetters(t, true);
  }

  function hasTraditional(t) {
    return /[\u9ad4\u81fa\u8207\u70ba\u9019\u500b\u4f86\u6703\u6642\u8aaa\u7121\u5f8c\u767c\u5b78\u66f8\u898b\u9ede\u958b\u95dc\u570b\u904e\u9084\u9032\u9078\u904b\u9801\u98a8\u98db\u98ef\u98f2\u9928\u99ac\u9b5a\u9ce5\u9f8d\u5340\u865f\u7db2\u7dda\u7d1a\u7d44\u7d50\u7d93\u7dad\u7e3d\u7de8\u807d\u8072\u806f\u8077\u842c\u83ef\u8449\u85cd\u8655\u885b\u88dd\u8907\u8996\u8a02\u8a55\u8a5e\u8a71\u8a72\u8a73\u8a9e\u8aa4\u8ab2\u8abf\u8acb\u8afe\u8b1d\u8b49\u8b58\u8b6f\u8b70\u8b80\u8b8a\u8ca1\u8cb7\u8ce3\u8cea\u8eca\u8edf\u8f03\u8f09\u8f2a\u8f38\u8fa6\u8fb2\u904a\u91ab\u91cb\u9280\u92fc\u9304\u9322\u932f\u9375\u9396\u9435\u9577\u96d9\u96e3\u96f2\u96fb\u97ff\u985e]/.test(t);
  }

  function should(t) {
    if (!t || t.length < 2) return false;
    if (protect(t)) return false;

    if (hasTraditional(t)) return true;

    var zh = (t.match(/[\u4e00-\u9fff]/g) || []).length;
    var nonLatinForeign = countNonLatinForeignLetters(t);

    if (zh > 0) return nonLatinForeign >= 2;

    var world = countWorldLanguageLetters(t);

    if (world >= 2) return true;

    return hasWorldLanguageLetter(t);
  }



  function pageMainlySimplifiedChinese() {
    if (!document.body) return false;
    if (originNodes.length || originEls.length || originAttrEls.length) return false;

    var text = String(document.body.innerText || document.body.textContent || '')
      .replace(/\s+/g, ' ')
      .slice(0, 9000);

    if (!text || text.length < 80) return false;

    var zh = (text.match(/[\u4e00-\u9fff]/g) || []).length;
    var world = countWorldLanguageLetters(text);

    if (hasTraditional(text)) return false;
    if (zh < 80) return false;

    var total = zh + world;
    if (!total) return false;

    return zh / total >= 0.55;
  }


  function simpleRichBlock(el) {
    if (!el || !el.getElementsByTagName) return false;

    var bad = el.querySelector && el.querySelector('pre,code,kbd,samp,var,script,style,textarea,input,select,button,svg,canvas,math,table');
    if (bad) return false;

    var all = el.getElementsByTagName('*');
    if (!all || !all.length) return false;

    for (var i = 0; i < all.length; i++) {
      var tag = all[i].tagName ? all[i].tagName.toLowerCase() : '';

      if (!/^(a|span|b|strong|i|em|u|mark|small|sub|sup|br)$/.test(tag)) {
        return false;
      }
    }

    return true;
  }

  function collectRichBlocks(list, used) {
    var els = document.querySelectorAll('p,blockquote,dd,figcaption,summary,h1,h2,h3,h4,h5,h6');

    for (var i = 0; i < els.length; i++) {
      var el = els[i];

      if (!simpleRichBlock(el)) continue;
      if (markEl && markEl.get(el) === el.textContent.trim()) continue;

      var text = el.textContent.trim();
      if (!text || text.length > 1600) continue;
      if (!should(text) && countNonLatinForeignLetters(text) < 2) continue;

      var r = rectOfEl(el);
      if (!r) continue;

      var html = el.innerHTML.trim();
      var key = htmlKey(html);

      if (cache[key]) {
        writeUnit({ type: 'html', el: el, text: key, top: r.top }, cache[key]);
        continue;
      }

      list.push({ type: 'html', el: el, text: key, top: r.top });

      var walker = document.createTreeWalker(el, NodeFilter.SHOW_TEXT, null, false);
      var n;
      while ((n = walker.nextNode())) {
        used.push(n);
      }

      if (list.length >= MAX_UNITS) return;
    }
  }

  function collectElements(list, used) {
    var els = document.querySelectorAll('p,li,h1,h2,h3,h4,h5,h6,dt,dd,figcaption,summary,blockquote');

    for (var i = 0; i < els.length; i++) {
      var el = els[i];
      if (markEl && markEl.get(el) === el.textContent.trim()) continue;
      if (hasUnsafeChild(el)) continue;

      var text = el.textContent.trim();
      if (!should(text) || text.length > 1200) continue;

      var r = rectOfEl(el);
      if (!r) continue;

      if (cache[text]) {
        writeUnit({ type: 'el', el: el, text: text, top: r.top }, cache[text]);
        continue;
      }

      list.push({ type: 'el', el: el, text: text, top: r.top });

      var walker = document.createTreeWalker(el, NodeFilter.SHOW_TEXT, null, false);
      var n;
      while ((n = walker.nextNode())) {
        used.push(n);
      }

      if (list.length >= MAX_UNITS) return;
    }
  }

  function collectNodes(list, usedMap) {
    var chars = 0;
    var w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT, null, false);
    var n;

    while ((n = w.nextNode())) {
      if (usedMap && usedMap.has(n)) continue;

      var raw = n.nodeValue || '';
      var text = raw.trim();

      if (markNode && markNode.get(n) === text) continue;
      if (!should(text)) continue;

      var r = rectOfNode(n);
      if (!r) continue;

      var head = raw.match(/^\s*/)[0];
      var tail = raw.match(/\s*$/)[0];

      if (cache[text]) {
        writeUnit({ type: 'node', node: n, raw: raw, text: text, head: head, tail: tail, top: r.top }, cache[text]);
        continue;
      }

      list.push({
        type: 'node',
        node: n,
        raw: raw,
        text: text,
        head: head,
        tail: tail,
        top: r.top
      });

      chars += text.length;

      if (list.length >= MAX_UNITS || chars >= MAX_CHARS) break;
    }
  }

  function plainForJudge(s) {
    return stripHtmlKey(s)
      .replace(/<[^>]+>/g, ' ')
      .replace(/&nbsp;/gi, ' ')
      .replace(/&amp;/gi, '&')
      .replace(/&lt;/gi, '<')
      .replace(/&gt;/gi, '>')
      .replace(/\s+/g, ' ')
      .trim();
  }

  function unitElement(unit) {
    if (!unit) return null;
    if (unit.el) return unit.el;
    if (unit.node && unit.node.parentElement) return unit.node.parentElement;
    return null;
  }

  function mostlyLatinNamedTitle(s) {
    s = String(s || '').trim();

    if (!s || /[.!?。！？,，:：；;]/.test(s)) return false;

    var words = s.split(/\s+/).filter(Boolean);
    if (words.length < 2 || words.length > 8) return false;

    var named = 0;

    for (var i = 0; i < words.length; i++) {
      var w = words[i].replace(/^[^\w]+|[^\w]+$/g, '');

      if (!w) return false;
      if (/^(?:and|or|of|for|to|in|on|with|the|a|an)$/i.test(w)) continue;
      if (/^[A-Z][A-Za-z0-9+.#_-]*$/.test(w)) {
        named++;
        continue;
      }

      return false;
    }

    return named >= 2;
  }

  function foreignUnitOnChinesePage(unit) {
    var s = plainForJudge(unit && unit.text);
    if (!s || s.length < 2) return false;

    if (/[\u4e00-\u9fff]/.test(s)) {
      return countNonLatinForeignLetters(s) >= 2;
    }

    if (protect(s)) return false;
    if (countWorldLanguageLetters(s) < 2) return false;

    var el = unitElement(unit);
    if (el && el.closest && el.closest('h1,h2') && mostlyLatinNamedTitle(s)) return false;

    return true;
  }

  function filterChinesePageForeignUnits(list) {
    var out = [];

    for (var i = 0; i < list.length; i++) {
      if (foreignUnitOnChinesePage(list[i])) {
        out.push(list[i]);
      }
    }

    return out;
  }

  function collect() {
    var list = [];
    var used = [];
    var usedMap = typeof WeakSet !== 'undefined' ? new WeakSet() : null;

    collectRichBlocks(list, used);
    collectElements(list, used);

    if (usedMap) {
      for (var i = 0; i < used.length; i++) {
        usedMap.add(used[i]);
      }
    }

    collectNodes(list, usedMap);

    list.sort(function (a, b) {
      var av = a.top >= 0 && a.top <= innerHeight ? 0 : 1;
      var bv = b.top >= 0 && b.top <= innerHeight ? 0 : 1;

      if (av !== bv) return av - bv;

      return Math.abs(a.top - innerHeight / 2) - Math.abs(b.top - innerHeight / 2);
    });

    var out = [];
    var chars = 0;

    for (var j = 0; j < list.length; j++) {
      out.push(list[j]);
      chars += list[j].text.length;

      if (out.length >= MAX_UNITS || chars >= MAX_CHARS) break;
    }

    return out;
  }

  function group(list) {
    var map = {};
    var texts = [];

    for (var i = 0; i < list.length; i++) {
      var t = list[i].text;

      if (!map[t]) {
        map[t] = [];
        texts.push(t);
      }

      map[t].push(list[i]);
    }

    return { map: map, texts: texts };
  }

  function chunks(texts) {
    var out = [];
    var cur = [];
    var len = 0;
    var mode = '';

    for (var i = 0; i < texts.length; i++) {
      var nextMode = modeOfText(texts[i]);

      if (cur.length && (nextMode !== mode || cur.length >= CHUNK_NODES || len + stripHtmlKey(texts[i]).length > CHUNK_CHARS)) {
        out.push(cur);
        cur = [];
        len = 0;
        mode = '';
      }

      if (!cur.length) mode = nextMode;

      cur.push(texts[i]);
      len += stripHtmlKey(texts[i]).length;
    }

    if (cur.length) out.push(cur);
    return out;
  }

  function traceId() {
    try {
      if (crypto && crypto.getRandomValues) {
        var a = new Uint8Array(16);
        crypto.getRandomValues(a);
        a[6] = (a[6] & 0x0f) | 0x40;
        a[8] = (a[8] & 0x3f) | 0x80;
        var h = [];
        for (var i = 0; i < a.length; i++) h.push(('0' + a[i].toString(16)).slice(-2));
        return h.slice(0, 4).join('') + '-' + h.slice(4, 6).join('') + '-' + h.slice(6, 8).join('') + '-' + h.slice(8, 10).join('') + '-' + h.slice(10).join('');
      }
    } catch (e) {}

    return String(Date.now()) + '-' + Math.random().toString(16).slice(2);
  }

  function trans(arr, retry, cb) {
    var body = [];
    var htmlMode = arr.length && isHtmlKey(arr[0]);
    var url = htmlMode ? API_HTML : API;

    for (var i = 0; i < arr.length; i++) {
      body.push({ Text: normalizeTranslateInput(stripHtmlKey(arr[i])) });
    }

    req({
      method: 'POST',
      url: url,
      headers: {
        'Content-Type': 'application/json',
        'Authorization': 'Bearer ' + token,
        'X-ClientTraceId': traceId()
      },
      data: JSON.stringify(body)
    }, function (r) {
      var data;

      if ((r.status === 401 || r.status === 403) && retry) {
        token = '';
        tokenTime = 0;

        getToken(function (err) {
          if (err) {
            markFailed(arr);
            cb(err);
            return;
          }

          trans(arr, false, cb);
        });
        return;
      }

      if (r.status < 200 || r.status >= 300) {
        markFailed(arr);
        cb('\u7ffb\u8bd1\u8bf7\u6c42\u5931\u8d25');
        return;
      }

      try {
        data = JSON.parse(r.responseText);
      } catch (e) {
        markFailed(arr);
        cb('\u8fd4\u56de\u683c\u5f0f\u9519\u8bef');
        return;
      }

      if (!Array.isArray(data)) {
        markFailed(arr);
        cb('\u8fd4\u56de\u683c\u5f0f\u9519\u8bef');
        return;
      }

      for (var i = 0; i < arr.length; i++) {
        var dst = data[i] && data[i].translations && data[i].translations[0] && data[i].translations[0].text;

        var srcRaw = stripHtmlKey(arr[i]);
        var srcNorm = normalizeTranslateInput(srcRaw);

        if (dst && cleanup(dst) !== cleanup(srcRaw) && cleanup(dst) !== cleanup(srcNorm)) {
          setCache(arr[i], dst);
          clearFailed(arr[i]);
        } else {
          failedTexts[arr[i]] = 1;
        }
      }

      cb('');
    }, function (e) {
      markFailed(arr);
      cb(e);
    });
  }

  function apply(g) {
    var n = 0;

    for (var src in g.map) {
      var dst = cache[src];
      if (!dst) continue;

      var units = g.map[src];

      for (var i = 0; i < units.length; i++) {
        writeUnit(units[i], dst);
        n++;
      }
    }

    return n;
  }

  function start(force) {
    if (!enabled) return;

    if (siteSkipped()) {
      if (force) say('\u672c\u7ad9\u5df2\u8df3\u8fc7\u81ea\u52a8\u7ffb\u8bd1');
      return;
    }

    var chineseMainPage = skipChinesePage && !siteAlways() && pageMainlySimplifiedChinese();

    if (running) {
      pending = true;
      return;
    }

    var list = collect();

    if (chineseMainPage) {
      list = filterChinesePageForeignUnits(list);
    }

    if (retryFailedOnce) {
      list = list.filter(function (u) {
        return u && failedTexts[u.text];
      });
      retryFailedOnce = false;
    }

    if (!list.length) {
      if (force) say('\u9644\u8fd1\u6ca1\u6709\u5f85\u7ffb\u8bd1\u6587\u672c');
      return;
    }

    var g = group(list);
    var cs = chunks(g.texts);
    var index = 0;
    var active = 0;
    var changed = 0;
    var stopped = false;

    running = true;
    pending = false;
    setButtonLabel('译');

    if (force) {
      say('\u7ffb\u8bd1\u4e2d ' + list.length + ' \u6bb5');
    }

    getToken(function (err) {
      if (err) {
        running = false;
        setButtonLabel(enabled ? '\u539f' : '\u8bd1');

        if (force) {
          say(err);
        }

        return;
      }

      function next() {
        if (stopped || !enabled) {
          running = false;
          setButtonLabel(enabled ? '\u539f' : '\u8bd1');
          return;
        }

        while (active < CONCURRENCY && index < cs.length) {
          active++;

          trans(cs[index++], true, function (e) {
            active--;

            if (e) {
              stopped = true;
              running = false;
              setButtonLabel(enabled ? '\u539f' : '\u8bd1');

              if (force) {
                say(e);
              }

              return;
            }

            if (!enabled) {
              running = false;
              setButtonLabel('\u8bd1');
              return;
            }

            changed = apply(g);

            if (index >= cs.length && active === 0) {
              running = false;
              setButtonLabel(enabled ? '\u539f' : '\u8bd1');

              if (force) {
                say('\u5b8c\u6210 ' + changed + ' \u6bb5');
              }

              if (pending && enabled) {
                if (enabled) schedule(false);
              }

              return;
            }

            next();
          });
        }
      }

      next();
    });
  }

  function schedule(force) {
    if (!enabled) return;

    clearTimeout(timer);
    timer = setTimeout(function () {
      start(force);
    }, force ? 0 : DELAY);
  }

  ui();
  setButtonLabel(enabled ? '\u539f' : '\u8bd1');
  if (enabled) getToken(function () {});
  schedule(false);

  function delayedSchedule(ms) {
    setTimeout(function () {
      if (enabled) schedule(false);
    }, ms);
  }

  addEventListener('load', function () {
    if (enabled) schedule(false);
  }, { passive: true });

  addEventListener('pageshow', function () {
    if (enabled) schedule(false);
  }, { passive: true });

  delayedSchedule(500);
  delayedSchedule(1500);
  delayedSchedule(3500);
  delayedSchedule(7000);


  addEventListener('pointerdown', function (e) {
    if (isMenuVisible() && !isOwnMutationTarget(e.target) && e.target !== btn) {
      hideMenu();
    }
  }, true);

  addEventListener('scroll', function () { if (enabled) schedule(false); }, { passive: true });
  addEventListener('resize', function () {
    if (btn && btn.style.left && btn.style.top) {
      snapButtonToEdge();
    }

    schedule(false);
  }, { passive: true });
  addEventListener('touchmove', function () { if (enabled) schedule(false); }, { passive: true });
  addEventListener('touchend', function () { if (enabled) schedule(false); }, { passive: true });

  function isOwnMutationTarget(n) {
    while (n && n !== document.documentElement) {
      if (n.getAttribute && n.getAttribute('data-ms-translator') === '1') return true;
      n = n.parentNode;
    }
    return false;
  }

  if (typeof MutationObserver !== 'undefined') {
    new MutationObserver(function (ms) {
      if (Date.now() < mutedUntil) return;

      for (var i = 0; i < ms.length; i++) {
        if (!isOwnMutationTarget(ms[i].target)) {
          if (enabled) {
            schedule(false);
          }
          return;
        }
      }
    }).observe(document.body || document.documentElement, {
      childList: true,
      subtree: true,
      characterData: true
    });
  }
})();

