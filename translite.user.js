// ==UserScript==
// @name         微软自动翻译
// @namespace    microsoft-auto-zh-hans-inline
// @version      1.7.4
// @description  基于 Microsoft Translator 的轻量网页自动翻译脚本，自动翻译为简体中文。
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
// @run-at       document-end
// ==/UserScript==

(function () {
  var AUTH = 'https://edge.microsoft.com/translate/auth';
  var API = 'https://api-edge.cognitive.microsofttranslator.com/translate?api-version=3.0&to=zh-Hans&textType=plain';
  var API_HTML = 'https://api-edge.cognitive.microsofttranslator.com/translate?api-version=3.0&to=zh-Hans&textType=html';

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
  var SET_PREFIX = 'ms_auto_zh_';
  var SITE_KEY = SET_PREFIX + 'site_' + location.hostname;
  var menu;
  var siteMode = settingGet(SITE_KEY, 'auto');
  var skipChinesePage = true;
  var phoneticGuard = true;
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
      var p;

      try {
        p = JSON.parse(v || '');
      } catch (e) {
        return;
      }

      if (!p || typeof p.left !== 'number' || typeof p.top !== 'number') return;

      var r = btn.getBoundingClientRect();
      var left = Math.max(4, Math.min(innerWidth - r.width - 4, p.left));
      var top = Math.max(4, Math.min(innerHeight - r.height - 4, p.top));

      btn.style.left = left + 'px';
      btn.style.top = top + 'px';
      btn.style.right = 'auto';
      btn.style.bottom = 'auto';
    });
  }

  function saveButtonPosition() {
    var r = btn.getBoundingClientRect();
    storeSet(POS_KEY, JSON.stringify({ left: r.left, top: r.top }));
  }

  function settingGet(k, d) {
    try {
      var v = localStorage.getItem(k);
      return v === null ? d : v;
    } catch (e) {
      return d;
    }
  }

  function settingSet(k, v) {
    try {
      localStorage.setItem(k, v);
    } catch (e) {}
  }

  function siteSkipped() {
    return siteMode === 'skip';
  }

  function siteAlways() {
    return siteMode === 'always';
  }

  function setSiteMode(v) {
    siteMode = v === 'skip' || v === 'always' ? v : 'auto';
    settingSet(SITE_KEY, siteMode);
  }

  function setButtonLabel(t) {
    if (!btnCanvas) return;

    var dpr = window.devicePixelRatio || 1;
    var size = 34;
    btnCanvas.width = size * dpr;
    btnCanvas.height = size * dpr;
    btnCanvas.style.width = size + 'px';
    btnCanvas.style.height = size + 'px';

    var c = btnCanvas.getContext && btnCanvas.getContext('2d');
    if (!c) return;

    c.setTransform(dpr, 0, 0, dpr, 0, 0);
    c.clearRect(0, 0, size, size);
    c.fillStyle = '#fff';
    c.font = '700 15px system-ui, -apple-system, BlinkMacSystemFont, sans-serif';
    c.textAlign = 'center';
    c.textBaseline = 'middle';
    c.fillText(t, size / 2, size / 2 + 0.5);
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
    var re = new RegExp('(?:' + cls + '[ \\t\ ]+){3,}' + cls, 'g');

    return String(s || '').replace(re, function (m) {
      var joined = m.replace(/[ \t ]+/g, '');

      if (joined.length < 4) return m;

      if (keepAcronym) {
        if (/^[A-Z]{2,8}$/.test(joined)) return m;
        if (/^(?:API|URL|URI|HTTP|HTTPS|HTML|CSS|XML|JSON|SQL|VPN|CPU|GPU|RAM|ROM|USB|DNS|TCP|UDP|SSH|SSL|TLS|APK|SDK|NDK|JDK|UI|UX)$/i.test(joined)) return m;
      }

      return m.replace(new RegExp('(' + cls + ')([ \\t\ ]+)(?=' + cls + ')', 'g'), function (_, ch, sp) {
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

  var HTML_PREFIX = ' html ';

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

  function ui() {
    btn = document.createElement('button');
    btn.setAttribute('data-ms-translator', '1');
    btn.setAttribute('aria-label', '\u539f\u6587/\u7ffb\u8bd1\u5207\u6362');
    btn.style.cssText = 'position:fixed;right:14px;bottom:86px;z-index:2147483647;width:34px;height:34px;padding:0;border:0;border-radius:50%;background:#111;color:#fff;box-sizing:border-box;display:flex;align-items:center;justify-content:center;-webkit-appearance:none;appearance:none;touch-action:none;user-select:none;-webkit-user-select:none;box-shadow:0 3px 10px rgba(0,0,0,.25);opacity:.86;';
    btnCanvas = document.createElement('canvas');
    btnCanvas.setAttribute('aria-hidden', 'true');
    btnCanvas.style.cssText = 'display:block;pointer-events:none;';
    btn.appendChild(btnCanvas);
    setButtonLabel('\u539f');
    btn.oncontextmenu = function (e) {
      e.preventDefault();
      e.stopPropagation();
      return false;
    };
    document.documentElement.appendChild(btn);
    restoreButtonPosition();
    drag(btn);

    tip = document.createElement('div');
    tip.setAttribute('data-ms-translator', '1');
    tip.style.cssText = 'position:fixed;left:50%;bottom:24px;transform:translateX(-50%);z-index:2147483647;display:none;max-width:82vw;padding:7px 10px;border-radius:999px;background:rgba(0,0,0,.76);color:#fff;font-size:12px;line-height:1.25;text-align:center;';
    document.documentElement.appendChild(tip);
  }

  function hideMenu() {
    if (menu) {
      menu.style.display = 'none';
    }
  }

  function menuButton(text, sub, fn) {
    var b = document.createElement('button');
    b.type = 'button';
    b.setAttribute('data-ms-translator', '1');
    b.style.cssText = 'display:flex;align-items:center;justify-content:space-between;width:100%;min-height:34px;padding:8px 10px;border:0;border-radius:10px;background:transparent;color:#111;font:500 13px system-ui,-apple-system,BlinkMacSystemFont,sans-serif;text-align:left;-webkit-appearance:none;appearance:none;';
    var l = document.createElement('span');
    l.textContent = text;
    var r = document.createElement('span');
    r.textContent = sub || '';
    r.style.cssText = 'margin-left:14px;color:#667085;font-weight:600;';
    b.appendChild(l);
    b.appendChild(r);
    b.addEventListener('click', function (e) {
      e.preventDefault();
      e.stopPropagation();
      fn && fn();
      renderMenu();
    }, true);
    return b;
  }

  function menuLine() {
    var d = document.createElement('div');
    d.style.cssText = 'height:1px;background:rgba(0,0,0,.08);margin:4px 0;';
    return d;
  }

  function renderMenu() {
    if (!menu) return;

    menu.innerHTML = '';

    var title = document.createElement('div');
    title.textContent = 'TransLite';
    title.style.cssText = 'padding:8px 10px 6px;color:#111;font:700 14px system-ui,-apple-system,BlinkMacSystemFont,sans-serif;';
    menu.appendChild(title);

    menu.appendChild(menuButton(enabled ? '\u663e\u793a\u539f\u6587' : '\u663e\u793a\u8bd1\u6587', enabled ? '\u539f\u6587' : '\u8bd1\u6587', function () {
      hideMenu();
      toggle();
    }));

    menu.appendChild(menuButton('\u5237\u65b0\u7ffb\u8bd1', '\u6e05\u7f13\u5b58', function () {
      hideMenu();
      cache = {};
      cacheKeys = [];
      failedTexts = {};
      pending = false;
      clearTimeout(timer);
      restoreOriginal();
      enabled = true;
      setButtonLabel('\u539f');
      say('\u5237\u65b0\u7ffb\u8bd1');
      schedule(true);
    }));

    menu.appendChild(menuButton('\u91cd\u8bd5\u5931\u8d25\u9879', failedCount() ? String(failedCount()) : '\u65e0', function () {
      hideMenu();

      if (!failedCount()) {
        say('\u6ca1\u6709\u5931\u8d25\u9879');
        return;
      }

      retryFailedOnce = true;
      enabled = true;
      setButtonLabel('\u539f');
      say('\u91cd\u8bd5\u5931\u8d25\u9879');
      schedule(true);
    }));

    menu.appendChild(menuLine());

    menu.appendChild(menuButton(siteSkipped() ? '\u6062\u590d\u672c\u7ad9\u7ffb\u8bd1' : '\u672c\u7ad9\u4e0d\u7ffb\u8bd1', siteSkipped() ? '\u6062\u590d' : '\u8df3\u8fc7', function () {
      hideMenu();

      if (siteSkipped()) {
        setSiteMode('auto');
        enabled = true;
        setButtonLabel('\u539f');
        say('\u5df2\u6062\u590d\u672c\u7ad9\u7ffb\u8bd1');
        schedule(true);
      } else {
        setSiteMode('skip');
        enabled = false;
        pending = false;
        clearTimeout(timer);
        restoreOriginal();
        setButtonLabel('\u8bd1');
        say('\u672c\u7ad9\u5df2\u8df3\u8fc7');
      }
    }));

    menu.appendChild(menuButton(siteAlways() ? '\u53d6\u6d88\u672c\u7ad9\u603b\u662f\u7ffb\u8bd1' : '\u672c\u7ad9\u603b\u662f\u7ffb\u8bd1', siteAlways() ? '\u53d6\u6d88' : '\u603b\u662f', function () {
      hideMenu();

      if (siteAlways()) {
        setSiteMode('auto');
        say('\u5df2\u53d6\u6d88\u672c\u7ad9\u603b\u662f\u7ffb\u8bd1');
      } else {
        setSiteMode('always');
        enabled = true;
        setButtonLabel('\u539f');
        say('\u672c\u7ad9\u603b\u662f\u7ffb\u8bd1');
        schedule(true);
      }
    }));

  }

  function showMenu() {
    if (!menu) {
      menu = document.createElement('div');
      menu.setAttribute('data-ms-translator', '1');
      menu.style.cssText = 'position:fixed;z-index:2147483647;width:210px;max-width:calc(100vw - 16px);padding:6px;border-radius:16px;background:rgba(255,255,255,.96);box-shadow:0 8px 30px rgba(0,0,0,.22);backdrop-filter:blur(10px);-webkit-backdrop-filter:blur(10px);user-select:none;-webkit-user-select:none;';
      document.documentElement.appendChild(menu);

      menu.addEventListener('pointerdown', function (e) {
        e.stopPropagation();
      }, true);
    }

    renderMenu();

    var br = btn.getBoundingClientRect();
    var w = 210;
    var left = Math.max(8, Math.min(innerWidth - w - 8, br.left - w + br.width));
    var top = Math.max(8, Math.min(innerHeight - 330, br.top - 310));

    if (br.top < 350) {
      top = Math.min(innerHeight - 330, br.bottom + 8);
    }

    menu.style.left = left + 'px';
    menu.style.top = top + 'px';
    menu.style.display = 'block';
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
      e.preventDefault();
      e.stopPropagation();

      if (e.stopImmediatePropagation) {
        e.stopImmediatePropagation();
      }
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
      }, 560);

      var r = el.getBoundingClientRect();
      sl = r.left;
      st = r.top;

      try {
        el.setPointerCapture(e.pointerId);
      } catch (err) {}
    }, true);

    el.addEventListener('pointermove', function (e) {
      if (!down) return;

      var dx = e.clientX - sx;
      var dy = e.clientY - sy;

      if (!active && Math.sqrt(dx * dx + dy * dy) >= 6) {
        clearTimeout(pressTimer);
        active = true;
        dragMoved = true;
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
        saveButtonPosition();
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
    tip.style.display = 'block';

    clearTimeout(tip._t);
    tip._t = setTimeout(function () {
      tip.style.display = 'none';
    }, 1100);
  }

  function toggle() {
    if (enabled) {
      enabled = false;
      pending = false;
      clearTimeout(timer);
      restoreOriginal();
      setButtonLabel('\u8bd1');
      say('\u5df2\u663e\u793a\u539f\u6587');
      return;
    }

    enabled = true;
    setButtonLabel('\u539f');
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
      headers: { 'Content-Type': 'application/json', 'Authorization': 'Bearer ' + token },
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
    setButtonLabel('…');

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
  if (enabled) getToken(function () {});
  schedule(false);


  addEventListener('pointerdown', function (e) {
    if (menu && menu.style.display !== 'none' && !isOwnMutationTarget(e.target) && e.target !== btn) {
      hideMenu();
    }
  }, true);

  addEventListener('scroll', function () { if (enabled) schedule(false); }, { passive: true });
  addEventListener('resize', function () {
    if (btn && btn.style.left && btn.style.top) {
      var r = btn.getBoundingClientRect();
      btn.style.left = Math.max(4, Math.min(innerWidth - r.width - 4, r.left)) + 'px';
      btn.style.top = Math.max(4, Math.min(innerHeight - r.height - 4, r.top)) + 'px';
      saveButtonPosition();
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
