/**
 * ═════════════════════════════════════════════════════════════════
 * FORESTBRAWL OWNER & ADMIN COMMAND DECK — CLIENT CONTROLLER
 * Full Reactive Telemetry, God Mode, Broadcast Studio, and Moderation
 * ═════════════════════════════════════════════════════════════════
 */

(() => {
  'use strict';

  // ── Application State ──────────────────────────────────────────
  const state = {
    token: localStorage.getItem('fb_owner_token') || '',
    user: null,
    dashboardData: null,
    usersList: [],
    cosmeticsData: null,
    activeTab: 'overview',
    selectedPlayer: null,
    sfxEnabled: localStorage.getItem('fb_admin_sfx') !== 'false',
    pollInterval: null,
    userSearchTimeout: null
  };

  // ── DOM Selectors ──────────────────────────────────────────────
  const $ = (s, el = document) => el.querySelector(s);
  const $$ = (s, el = document) => [...el.querySelectorAll(s)];

  // ── Audio Synthesizer (Web Audio API) ──────────────────────────
  let audioCtx = null;
  function getAudioCtx() {
    if (!audioCtx) {
      const AudioContext = window.AudioContext || window.webkitAudioContext;
      if (AudioContext) audioCtx = new AudioContext();
    }
    if (audioCtx && audioCtx.state === 'suspended') {
      audioCtx.resume();
    }
    return audioCtx;
  }

  function playSoundTone(freq, duration = 0.08, type = 'sine', gainVal = 0.15) {
    if (!state.sfxEnabled) return;
    try {
      const ctx = getAudioCtx();
      if (!ctx) return;
      const osc = ctx.createOscillator();
      const gain = ctx.createGain();
      osc.type = type;
      osc.frequency.setValueAtTime(freq, ctx.currentTime);
      gain.gain.setValueAtTime(gainVal, ctx.currentTime);
      gain.gain.exponentialRampToValueAtTime(0.0001, ctx.currentTime + duration);
      osc.connect(gain);
      gain.connect(ctx.destination);
      osc.start();
      osc.stop(ctx.currentTime + duration);
    } catch (_) {}
  }

  const sfx = {
    click: () => playSoundTone(880, 0.04, 'sine', 0.1),
    success: () => {
      playSoundTone(523.25, 0.08, 'triangle', 0.15);
      setTimeout(() => playSoundTone(659.25, 0.08, 'triangle', 0.15), 60);
      setTimeout(() => playSoundTone(783.99, 0.12, 'triangle', 0.18), 120);
    },
    error: () => {
      playSoundTone(220, 0.12, 'sawtooth', 0.2);
      setTimeout(() => playSoundTone(180, 0.16, 'sawtooth', 0.22), 80);
    },
    gong: () => {
      playSoundTone(440, 0.3, 'sine', 0.2);
      setTimeout(() => playSoundTone(554.37, 0.35, 'triangle', 0.2), 60);
    }
  };

  // ── Toast Notification System ──────────────────────────────────
  function showToast(message, type = 'success', duration = 3200) {
    const container = $('#toast-container');
    if (!container) return;

    const el = document.createElement('div');
    el.className = `toast-msg ${type === 'error' ? 'toast-error' : type === 'warning' ? 'toast-warning' : ''}`;
    
    const icon = type === 'error' ? '⚠️' : type === 'warning' ? '🔔' : '✨';
    el.innerHTML = `<span class="toast-icon">${icon}</span><span>${escapeHtml(message)}</span>`;
    container.appendChild(el);

    requestAnimationFrame(() => el.classList.add('show'));

    if (type === 'error') sfx.error();
    else sfx.success();

    setTimeout(() => {
      el.classList.remove('show');
      setTimeout(() => el.remove(), 320);
    }, duration);
  }

  // ── API Fetch Client ───────────────────────────────────────────
  async function api(path, options = {}) {
    const headers = {
      'Content-Type': 'application/json',
      ...(options.headers || {})
    };
    if (state.token) {
      headers.Authorization = `Bearer ${state.token}`;
    }

    try {
      const res = await fetch(path, { ...options, headers });
      const data = await res.json().catch(() => ({ error: 'Sunucudan geçersiz JSON yanıtı.' }));
      if (!res.ok) {
        throw new Error(data.error || `İşlem başarısız (HTTP ${res.status}).`);
      }
      return data;
    } catch (err) {
      if (err.message && err.message.includes('Owner oturumu')) {
        showLoginView();
      }
      throw err;
    }
  }

  // ── View Switching ─────────────────────────────────────────────
  function showLoginView() {
    state.token = '';
    state.user = null;
    localStorage.removeItem('fb_owner_token');
    stopPolling();
    $('#app-view').classList.add('hidden');
    $('#login-view').classList.remove('hidden');
    $('#login-error').classList.add('hidden');
  }

  function showAppView(user) {
    state.user = user;
    $('#login-view').classList.add('hidden');
    $('#app-view').classList.remove('hidden');

    const name = user.username || 'Owner';
    $('#owner-display-name').textContent = name;
    $('#owner-avatar').textContent = name.charAt(0).toUpperCase();

    // Initial data fetch
    loadDashboard();
    startPolling();
  }

  // ── Authentication Handlers ────────────────────────────────────
  $('#login-form').addEventListener('submit', async (e) => {
    e.preventDefault();
    const btn = $('#login-submit-btn');
    const errBox = $('#login-error');
    errBox.classList.add('hidden');

    const username = $('#username').value.trim();
    const password = $('#password').value;

    if (!username || !password) {
      errBox.textContent = 'Kullanıcı adı ve şifre gereklidir.';
      errBox.classList.remove('hidden');
      return;
    }

    btn.disabled = true;
    btn.querySelector('span').textContent = 'Doğrulanıyor...';

    try {
      const res = await api('/api/owner/login', {
        method: 'POST',
        body: JSON.stringify({ username, password })
      });

      state.token = res.token;
      localStorage.setItem('fb_owner_token', state.token);
      sfx.success();
      showToast(`Hoş geldin, ${res.user.username}! Komuta merkezi hazır.`);
      showAppView(res.user);
    } catch (err) {
      sfx.error();
      errBox.textContent = err.message || 'Giriş başarısız.';
      errBox.classList.remove('hidden');
    } finally {
      btn.disabled = false;
      btn.querySelector('span').textContent = 'Panele Güvenli Bağlan';
    }
  });

  $('#toggle-pwd-btn').addEventListener('click', () => {
    const input = $('#password');
    const isPwd = input.type === 'password';
    input.type = isPwd ? 'text' : 'password';
    $('#toggle-pwd-btn').textContent = isPwd ? '🔒' : '👁️';
    sfx.click();
  });

  $('#logout-btn').addEventListener('click', async () => {
    sfx.click();
    try {
      await api('/api/owner/logout', { method: 'POST' });
    } catch (_) {}
    showToast('Güvenli çıkış yapıldı.');
    showLoginView();
  });

  // ── Tab Management ─────────────────────────────────────────────
  const TAB_HEADINGS = {
    overview: 'Sunucu Nabzı & Canlı Telemetri',
    players: 'Canlı Oyuncular & God Mode',
    broadcast: 'Duyuru & Oyun İçi Yayın Stüdyosu',
    world: 'Dünya Kuralları & Dinamik Ayarlar',
    users: 'Kayıtlı Oyuncu Hesapları & Moderasyon',
    cosmetics: 'Kozmetik Envanteri & Fiyat / Rarity Yönetimi',
    audit: 'Güvenlik Logları & Aktif Yasaklamalar'
  };

  $$('.nav-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      const tab = btn.dataset.tab;
      if (!tab || tab === state.activeTab) return;
      sfx.click();
      setActiveTab(tab);
    });
  });

  function setActiveTab(tab) {
    state.activeTab = tab;

    $$('.nav-btn').forEach(b => b.classList.toggle('active', b.dataset.tab === tab));
    $$('.tab-pane').forEach(p => p.classList.toggle('hidden', p.id !== `tab-${tab}`));

    $('#active-tab-title').textContent = tab.toUpperCase();
    $('#view-heading').textContent = TAB_HEADINGS[tab] || 'Komuta Merkezi';

    // Refresh specific tab data when activated
    if (tab === 'users') loadUsers();
    else if (tab === 'cosmetics') loadCosmetics();
    else if (tab === 'players') renderPlayersTable();
    else if (tab === 'audit') renderAuditTimeline();
  }

  // ── Sound FX Toggle ────────────────────────────────────────────
  $('#sfx-toggle-btn').addEventListener('click', () => {
    state.sfxEnabled = !state.sfxEnabled;
    localStorage.setItem('fb_admin_sfx', String(state.sfxEnabled));
    $('#sfx-icon').textContent = state.sfxEnabled ? '🔊' : '🔇';
    if (state.sfxEnabled) sfx.click();
    showToast(state.sfxEnabled ? 'Panel sesleri açıldı.' : 'Panel sessize alındı.');
  });
  $('#sfx-icon').textContent = state.sfxEnabled ? '🔊' : '🔇';

  // ── Polling & Dashboard Data Loader ────────────────────────────
  $('#refresh-btn').addEventListener('click', () => {
    sfx.click();
    loadDashboard(true);
  });

  function startPolling() {
    stopPolling();
    state.pollInterval = setInterval(() => {
      if (document.visibilityState === 'visible' && state.token) {
        loadDashboard(false);
      }
    }, 3500);
  }

  function stopPolling() {
    if (state.pollInterval) {
      clearInterval(state.pollInterval);
      state.pollInterval = null;
    }
  }

  async function loadDashboard(showManualToast = false) {
    try {
      const data = await api('/api/owner/dashboard');
      state.dashboardData = data;

      renderHudPills(data.stats);
      renderOverviewTab(data);
      if (state.activeTab === 'players') renderPlayersTable();
      if (state.activeTab === 'audit') renderAuditTimeline();

      if (showManualToast) {
        showToast('Veriler güncellendi.');
      }
    } catch (err) {
      console.warn('[AdminDashboard] poll failed:', err.message);
    }
  }

  // ── Render Helpers ─────────────────────────────────────────────
  function formatUptime(seconds) {
    const s = Math.floor(seconds || 0);
    const h = Math.floor(s / 3600);
    const m = Math.floor((s % 3600) / 60);
    const sec = s % 60;
    if (h > 0) return `${h}s ${m}d`;
    if (m > 0) return `${m}d ${sec}sn`;
    return `${sec}sn`;
  }

  function renderHudPills(stats) {
    if (!stats) return;
    $('#server-uptime-label').textContent = formatUptime(stats.uptimeSec);
    $('#server-ram-label').textContent = `${stats.ramMb || 0} MB`;
    $('#sys-rss-stat').textContent = `${stats.ramMb || 0} MB`;
    $('#sys-heap-stat').textContent = `${stats.heapMb || 0} MB`;
    $('#sys-banned-stat').textContent = `${stats.bannedCount || 0} IP / Kullanıcı`;
    $('#nav-badge-online').textContent = stats.online || 0;
  }

  function renderOverviewTab(data) {
    const s = data.stats || {};
    const c = data.config || {};

    $('#stat-online').textContent = s.online ?? 0;
    $('#stat-online-detail').textContent = `${s.online ?? 0} aktif savaşta`;
    $('#stat-mobs').textContent = s.mobs ?? 0;
    $('#stat-buildings').textContent = s.buildings ?? 0;
    $('#stat-users').textContent = s.registeredUsers ?? 0;
    $('#stat-clans').textContent = s.clans ?? 0;
    $('#stat-parties-badge').textContent = `${s.parties ?? 0} aktif parti`;

    // Quick toggles in overview hero
    const maintToggle = $('#quick-maintenance-toggle');
    maintToggle.checked = Boolean(c.maintenance);
    $('#quick-maint-status').textContent = c.maintenance ? 'AKTİF (Girişler Kapalı)' : 'Kapalı';
    $('#quick-maint-status').style.color = c.maintenance ? 'var(--crimson-light)' : 'var(--text-dim)';

    const pvpToggle = $('#quick-pvp-toggle');
    pvpToggle.checked = c.pvpEnabled !== false;
    $('#quick-pvp-status').textContent = (c.pvpEnabled !== false) ? 'Açık (Savaş Var)' : 'Kapalı (Barış)';
    $('#quick-pvp-status').style.color = (c.pvpEnabled !== false) ? 'var(--emerald-light)' : 'var(--amber-light)';

    // World settings tab inputs
    $('#cfg-maintenance').checked = Boolean(c.maintenance);
    $('#cfg-pvp').checked = c.pvpEnabled !== false;
    
    ['xpRate', 'mobSpawnMultiplier', 'resourceRespawnMultiplier'].forEach(k => {
      const val = c[k] !== undefined ? Number(c[k]) : 1;
      const idMap = { xpRate: 'xprate', mobSpawnMultiplier: 'mobrate', resourceRespawnMultiplier: 'resrate' };
      const el = $(`#cfg-${idMap[k]}`);
      const valEl = $(`#cfg-${idMap[k]}-val`);
      if (el) el.value = val;
      if (valEl) valEl.textContent = `${val.toFixed(1)}x`;
    });

    // Quick audit feed
    const auditList = data.audit || [];
    const feedEl = $('#quick-audit-feed');
    if (auditList.length === 0) {
      feedEl.innerHTML = '<div class="empty-feed">Henüz yönetici hareketi yok.</div>';
    } else {
      feedEl.innerHTML = auditList.slice(0, 6).map(item => `
        <div class="audit-chip">
          <div><b>${escapeHtml(item.action)}</b> · <span class="muted">${escapeHtml(item.username || 'system')}</span></div>
          <time>${new Date(item.at).toLocaleTimeString('tr-TR')}</time>
        </div>
      `).join('');
    }

    const layout = c.mainMenuLayout || getLayoutEditorDefaults();
    renderMainMenuLayoutEditor(layout);
  }

  const mainMenuLayoutEditor = {
    activeKey: null,
    mode: null,
    pointerId: null,
    originX: 0,
    originY: 0,
    startRect: null,
    viewport: null,
    items: new Map(),
    orientation: 'landscape',
    layoutCache: { portrait: {}, landscape: {} }
  };

  function getCurrentLayoutMode() {
    return window.matchMedia && window.matchMedia('(orientation: portrait)').matches ? 'portrait' : 'landscape';
  }

  function getLayoutEditorDefaults(mode = 'landscape') {
    if (mode === 'portrait') {
      return {
        leftEventsContainer: { xPercent: 10, yPercent: 20, widthPercent: 82, heightPercent: 18 },
        headerMain: { xPercent: 50, yPercent: 8, widthPercent: 96, heightPercent: 12 },
        headerRightPanel: { xPercent: 82, yPercent: 8, widthPercent: 18, heightPercent: 22 },
        profileHud: { xPercent: 26, yPercent: 8, widthPercent: 42, heightPercent: 10 },
        inviteEvent: { xPercent: 18, yPercent: 27, widthPercent: 34, heightPercent: 20 },
        creatorEvent: { xPercent: 18, yPercent: 48, widthPercent: 34, heightPercent: 20 },
        mainMenu: { xPercent: 50, yPercent: 58, widthPercent: 86, heightPercent: 50 },
        nameInput: { xPercent: 50, yPercent: 34, widthPercent: 78, heightPercent: 9 },
        activePetBtn: { xPercent: 50, yPercent: 48, widthPercent: 78, heightPercent: 16 },
        playBtn: { xPercent: 50, yPercent: 65, widthPercent: 88, heightPercent: 15 },
        actionButtons: { xPercent: 50, yPercent: 77, widthPercent: 82, heightPercent: 12 },
        profileModal: { xPercent: 50, yPercent: 50, widthPercent: 90, heightPercent: 72 },
        cosmeticsModal: { xPercent: 50, yPercent: 50, widthPercent: 94, heightPercent: 82 },
        shopModal: { xPercent: 50, yPercent: 50, widthPercent: 96, heightPercent: 86 },
        levelRewardsModal: { xPercent: 50, yPercent: 50, widthPercent: 90, heightPercent: 72 },
        newsModal: { xPercent: 50, yPercent: 50, widthPercent: 88, heightPercent: 64 },
        friendInviteModal: { xPercent: 50, yPercent: 50, widthPercent: 94, heightPercent: 84 },
        creatorEventModal: { xPercent: 50, yPercent: 50, widthPercent: 96, heightPercent: 86 },
        leadersModal: { xPercent: 50, yPercent: 50, widthPercent: 92, heightPercent: 78 },
        challengesModal: { xPercent: 50, yPercent: 50, widthPercent: 92, heightPercent: 78 },
        dailyRewardModal: { xPercent: 50, yPercent: 50, widthPercent: 92, heightPercent: 70 },
        partyModal: { xPercent: 50, yPercent: 50, widthPercent: 88, heightPercent: 64 },
        helpModal: { xPercent: 50, yPercent: 50, widthPercent: 88, heightPercent: 64 }
      };
    }

    return {
      leftEventsContainer: { xPercent: 8, yPercent: 22, widthPercent: 26, heightPercent: 35 },
      headerMain: { xPercent: 50, yPercent: 8, widthPercent: 98, heightPercent: 14 },
      headerRightPanel: { xPercent: 80, yPercent: 18, widthPercent: 22, heightPercent: 30 },
      profileHud: { xPercent: 21, yPercent: 8, widthPercent: 26, heightPercent: 10 },
      inviteEvent: { xPercent: 12, yPercent: 32, widthPercent: 22, heightPercent: 26 },
      creatorEvent: { xPercent: 12, yPercent: 62, widthPercent: 22, heightPercent: 26 },
      mainMenu: { xPercent: 50, yPercent: 50, widthPercent: 38, heightPercent: 72 },
      nameInput: { xPercent: 50, yPercent: 31, widthPercent: 68, heightPercent: 8 },
      activePetBtn: { xPercent: 50, yPercent: 45, widthPercent: 68, heightPercent: 18 },
      playBtn: { xPercent: 50, yPercent: 60, widthPercent: 78, heightPercent: 16 },
      actionButtons: { xPercent: 50, yPercent: 74, widthPercent: 68, heightPercent: 14 },
      profileModal: { xPercent: 50, yPercent: 50, widthPercent: 34, heightPercent: 72 },
      cosmeticsModal: { xPercent: 50, yPercent: 50, widthPercent: 54, heightPercent: 82 },
      shopModal: { xPercent: 50, yPercent: 50, widthPercent: 64, heightPercent: 86 },
      levelRewardsModal: { xPercent: 50, yPercent: 50, widthPercent: 38, heightPercent: 72 },
      newsModal: { xPercent: 50, yPercent: 50, widthPercent: 34, heightPercent: 64 },
      friendInviteModal: { xPercent: 50, yPercent: 50, widthPercent: 46, heightPercent: 84 },
      creatorEventModal: { xPercent: 50, yPercent: 50, widthPercent: 54, heightPercent: 86 },
      leadersModal: { xPercent: 50, yPercent: 50, widthPercent: 42, heightPercent: 78 },
      challengesModal: { xPercent: 50, yPercent: 50, widthPercent: 42, heightPercent: 78 },
      dailyRewardModal: { xPercent: 50, yPercent: 50, widthPercent: 40, heightPercent: 70 },
      partyModal: { xPercent: 50, yPercent: 50, widthPercent: 32, heightPercent: 64 },
      helpModal: { xPercent: 50, yPercent: 50, widthPercent: 34, heightPercent: 64 }
    };
  }

  function resolveLayoutForMode(layout, mode = null) {
    const selectedMode = mode || mainMenuLayoutEditor.orientation || getCurrentLayoutMode();
    if (layout && typeof layout === 'object' && !Array.isArray(layout) && (layout.portrait || layout.landscape)) {
      return sanitizeMainMenuLayout(layout[selectedMode] || layout.landscape || layout.portrait || getLayoutEditorDefaults(selectedMode), selectedMode);
    }
    return sanitizeMainMenuLayout(layout || getLayoutEditorDefaults(selectedMode), selectedMode);
  }

  function clampPercentage(value, min = 0, max = 100) {
    if (!Number.isFinite(value)) return min;
    return Math.min(Math.max(value, min), max);
  }

  function sanitizeMainMenuLayout(layout, mode = null) {
    const defaults = getLayoutEditorDefaults(mode || mainMenuLayoutEditor.orientation || getCurrentLayoutMode());
    const output = {};
    for (const [key, fallback] of Object.entries(defaults)) {
      const value = layout && layout[key] ? layout[key] : fallback;
      output[key] = {
        xPercent: clampPercentage(Number(value.xPercent ?? value.x ?? fallback.xPercent), 0, 100),
        yPercent: clampPercentage(Number(value.yPercent ?? value.y ?? fallback.yPercent), 0, 100),
        widthPercent: clampPercentage(Number(value.widthPercent ?? value.w ?? fallback.widthPercent), 8, 100),
        heightPercent: clampPercentage(Number(value.heightPercent ?? value.h ?? fallback.heightPercent), 8, 100)
      };
    }
    return output;
  }

  function buildMainMenuLayoutPayload() {
    const selectedMode = mainMenuLayoutEditor.orientation || getCurrentLayoutMode();
    const base = {
      portrait: mainMenuLayoutEditor.layoutCache.portrait || getLayoutEditorDefaults('portrait'),
      landscape: mainMenuLayoutEditor.layoutCache.landscape || getLayoutEditorDefaults('landscape')
    };

    if (mainMenuLayoutEditor.items.size) {
      const activeLayout = Object.fromEntries([...mainMenuLayoutEditor.items.entries()].map(([key, item]) => [key, item.config]));
      base[selectedMode] = sanitizeMainMenuLayout(activeLayout, selectedMode);
    }

    return {
      portrait: sanitizeMainMenuLayout(base.portrait, 'portrait'),
      landscape: sanitizeMainMenuLayout(base.landscape, 'landscape')
    };
  }

  function setEditorLayoutFromPage() {
    const selectors = {
      leftEventsContainer: '#left-events-container',
      headerRightPanel: '#header-right-panel',
      mainMenu: '#main-menu',
      nameInput: '#name-input',
      activePetBtn: '#active-pet-btn',
      playBtn: '#play-btn',
      actionButtons: '#action-buttons-grid'
    };
    const viewportW = window.innerWidth || document.documentElement.clientWidth || 1;
    const viewportH = window.innerHeight || document.documentElement.clientHeight || 1;
    const selectedMode = mainMenuLayoutEditor.orientation || getCurrentLayoutMode();
    const next = { ...(mainMenuLayoutEditor.layoutCache[selectedMode] || getLayoutEditorDefaults(selectedMode)) };

    Object.entries(selectors).forEach(([key, selector]) => {
      const el = document.querySelector(selector);
      if (!el) return;
      const rect = el.getBoundingClientRect();
      next[key] = {
        xPercent: clampPercentage(((rect.left + rect.width / 2) / viewportW) * 100, 0, 100),
        yPercent: clampPercentage(((rect.top + rect.height / 2) / viewportH) * 100, 0, 100),
        widthPercent: clampPercentage((rect.width / viewportW) * 100, 8, 100),
        heightPercent: clampPercentage((rect.height / viewportH) * 100, 8, 100)
      };
    });

    mainMenuLayoutEditor.layoutCache[selectedMode] = sanitizeMainMenuLayout(next, selectedMode);
    renderMainMenuLayoutEditor(mainMenuLayoutEditor.layoutCache, selectedMode);
    return {
      portrait: sanitizeMainMenuLayout(mainMenuLayoutEditor.layoutCache.portrait || getLayoutEditorDefaults('portrait'), 'portrait'),
      landscape: sanitizeMainMenuLayout(mainMenuLayoutEditor.layoutCache.landscape || getLayoutEditorDefaults('landscape'), 'landscape')
    };
  }

  function syncLayoutEditorItem(key, config) {
    const viewport = mainMenuLayoutEditor.viewport;
    const item = mainMenuLayoutEditor.items.get(key);
    if (!viewport || !item) return;

    const rect = {
      left: (config.xPercent / 100) * viewport.clientWidth - (config.widthPercent / 100) * viewport.clientWidth / 2,
      top: (config.yPercent / 100) * viewport.clientHeight - (config.heightPercent / 100) * viewport.clientHeight / 2,
      width: (config.widthPercent / 100) * viewport.clientWidth,
      height: (config.heightPercent / 100) * viewport.clientHeight
    };

    item.el.style.left = `${rect.left}px`;
    item.el.style.top = `${rect.top}px`;
    item.el.style.width = `${rect.width}px`;
    item.el.style.height = `${rect.height}px`;
    item.config = config;
    item.label.textContent = key;
  }

  function setLayoutEditorFullscreen(enabled) {
    const panel = document.querySelector('.layout-editor-panel');
    if (!panel) return;

    panel.classList.toggle('is-fullscreen', enabled);
    document.body.classList.toggle('layout-editor-fullscreen', enabled);

    const toggleBtn = document.getElementById('toggle-layout-fullscreen-btn');
    if (toggleBtn) {
      toggleBtn.textContent = enabled ? 'Tam Ekrandan Çık' : 'Tam Ekran';
    }
  }

  function renderMainMenuLayoutEditor(layout = null, mode = null) {
    const viewport = document.getElementById('layout-editor-viewport');
    if (!viewport) return;

    const selectedMode = mode || mainMenuLayoutEditor.orientation || getCurrentLayoutMode();
    mainMenuLayoutEditor.orientation = selectedMode;
    mainMenuLayoutEditor.viewport = viewport;
    mainMenuLayoutEditor.items.clear();
    viewport.innerHTML = '';

    const config = resolveLayoutForMode(layout, selectedMode);
    mainMenuLayoutEditor.layoutCache[selectedMode] = config;

    const modeButtons = document.querySelectorAll('.mode-btn');
    modeButtons.forEach((btn) => btn.classList.toggle('active', btn.dataset.layoutMode === selectedMode));

    const palette = {
      leftEventsContainer: 'rgba(251, 191, 36, 0.34)',
      headerMain: 'rgba(14, 165, 233, 0.22)',
      headerRightPanel: 'rgba(168, 85, 247, 0.34)',
      profileHud: 'rgba(234, 179, 8, 0.28)',
      inviteEvent: 'rgba(249, 115, 22, 0.32)',
      creatorEvent: 'rgba(192, 132, 252, 0.32)',
      mainMenu: 'rgba(34, 197, 94, 0.22)',
      nameInput: 'rgba(59, 130, 246, 0.34)',
      activePetBtn: 'rgba(236, 72, 153, 0.28)',
      playBtn: 'rgba(239, 68, 68, 0.28)',
      actionButtons: 'rgba(14, 165, 233, 0.28)',
      profileModal: 'rgba(234, 179, 8, 0.2)',
      cosmeticsModal: 'rgba(236, 72, 153, 0.2)',
      shopModal: 'rgba(245, 158, 11, 0.22)',
      levelRewardsModal: 'rgba(34, 197, 94, 0.2)',
      newsModal: 'rgba(59, 130, 246, 0.22)',
      friendInviteModal: 'rgba(249, 115, 22, 0.24)',
      creatorEventModal: 'rgba(168, 85, 247, 0.24)',
      leadersModal: 'rgba(250, 204, 21, 0.2)',
      challengesModal: 'rgba(239, 68, 68, 0.2)',
      dailyRewardModal: 'rgba(20, 184, 166, 0.2)',
      partyModal: 'rgba(59, 130, 246, 0.2)',
      helpModal: 'rgba(148, 163, 184, 0.2)'
    };

    Object.entries(config).forEach(([key, itemConfig]) => {
      const el = document.createElement('div');
      el.className = 'layout-editor-item';
      el.style.background = palette[key] || 'rgba(255,255,255,0.08)';
      el.style.borderColor = 'rgba(255,255,255,0.5)';

      const resizeHandle = document.createElement('div');
      resizeHandle.className = 'layout-editor-resize-handle';
      resizeHandle.title = `${key} boyutlandır`;
      el.appendChild(resizeHandle);

      const label = document.createElement('span');
      label.textContent = key;
      label.className = 'layout-editor-label';
      el.appendChild(label);

      el.addEventListener('pointerdown', (event) => {
        if (event.target.closest('.layout-editor-resize-handle')) return;
        event.preventDefault();
        mainMenuLayoutEditor.activeKey = key;
        mainMenuLayoutEditor.mode = 'move';
        mainMenuLayoutEditor.pointerId = event.pointerId;
        mainMenuLayoutEditor.originX = event.clientX;
        mainMenuLayoutEditor.originY = event.clientY;
        mainMenuLayoutEditor.startRect = { ...itemConfig };
        el.setPointerCapture(event.pointerId);
      });

      resizeHandle.addEventListener('pointerdown', (event) => {
        event.preventDefault();
        event.stopPropagation();
        mainMenuLayoutEditor.activeKey = key;
        mainMenuLayoutEditor.mode = 'resize';
        mainMenuLayoutEditor.pointerId = event.pointerId;
        mainMenuLayoutEditor.originX = event.clientX;
        mainMenuLayoutEditor.originY = event.clientY;
        mainMenuLayoutEditor.startRect = { ...itemConfig };
        el.setPointerCapture(event.pointerId);
      });

      el.addEventListener('pointermove', (event) => {
        if (mainMenuLayoutEditor.activeKey !== key || mainMenuLayoutEditor.pointerId !== event.pointerId) return;

        const dx = (event.clientX - mainMenuLayoutEditor.originX) / viewport.clientWidth * 100;
        const dy = (event.clientY - mainMenuLayoutEditor.originY) / viewport.clientHeight * 100;
        let next = { ...mainMenuLayoutEditor.startRect };

        if (mainMenuLayoutEditor.mode === 'move') {
          next = {
            ...next,
            xPercent: clampPercentage(mainMenuLayoutEditor.startRect.xPercent + dx, 0, 100),
            yPercent: clampPercentage(mainMenuLayoutEditor.startRect.yPercent + dy, 0, 100)
          };
        } else if (mainMenuLayoutEditor.mode === 'resize') {
          next = {
            ...next,
            widthPercent: clampPercentage(mainMenuLayoutEditor.startRect.widthPercent + dx * 1.35, 8, 100),
            heightPercent: clampPercentage(mainMenuLayoutEditor.startRect.heightPercent + dy * 1.35, 8, 100)
          };
        }

        syncLayoutEditorItem(key, next);
        mainMenuLayoutEditor.items.get(key).config = next;
      });

      const resetInteractionState = () => {
        mainMenuLayoutEditor.pointerId = null;
        mainMenuLayoutEditor.activeKey = null;
        mainMenuLayoutEditor.mode = null;
        mainMenuLayoutEditor.startRect = null;
      };

      el.addEventListener('pointerup', resetInteractionState);
      el.addEventListener('pointercancel', resetInteractionState);

      el.addEventListener('pointerleave', () => {
        if (mainMenuLayoutEditor.pointerId === null) return;
        resetInteractionState();
      });

      mainMenuLayoutEditor.items.set(key, { el, label, config: itemConfig });
      syncLayoutEditorItem(key, itemConfig);
      viewport.appendChild(el);
    });
  }

  async function saveAndApplyMainMenuLayout() {
    const layout = buildMainMenuLayoutPayload();
    localStorage.setItem('fb_main_menu_layout', JSON.stringify(layout));
    const payload = { mainMenuLayout: layout };
    try {
      await api('/api/owner/config', {
        method: 'POST',
        body: JSON.stringify(payload)
      });
      if (window.parent && window.parent !== window) {
        window.parent.postMessage({ type: 'forestbrawl-main-layout', layout }, '*');
      }
      showToast('🧭 Ana ekran düzeni kaydedildi ve canlı uygulandı.');
      loadDashboard();
    } catch (err) {
      showToast(err.message || 'Ana ekran düzeni kaydedilemedi.', 'error');
    }
  }

  function applyMainMenuLayoutOnPublicPage(layout) {
    const config = sanitizeMainMenuLayout(layout || getLayoutEditorDefaults());
    const viewportW = window.innerWidth || document.documentElement.clientWidth || 1;
    const viewportH = window.innerHeight || document.documentElement.clientHeight || 1;

    const viewMap = {
      leftEventsContainer: document.getElementById('left-events-container'),
      headerRightPanel: document.getElementById('header-right-panel'),
      mainMenu: document.getElementById('main-menu'),
      nameInput: document.getElementById('name-input'),
      activePetBtn: document.getElementById('active-pet-btn'),
      playBtn: document.getElementById('play-btn'),
      actionButtons: document.getElementById('action-buttons-grid')
    };

    Object.entries(viewMap).forEach(([key, el]) => {
      if (!el || !config[key]) return;
      const item = config[key];
      const left = ((item.xPercent / 100) * viewportW) - ((item.widthPercent / 100) * viewportW) / 2;
      const top = ((item.yPercent / 100) * viewportH) - ((item.heightPercent / 100) * viewportH) / 2;

      if (key === 'mainMenu') {
        el.style.position = 'fixed';
        el.style.left = `${left}px`;
        el.style.top = `${top}px`;
        el.style.width = `${(item.widthPercent / 100) * viewportW}px`;
        el.style.height = `${(item.heightPercent / 100) * viewportH}px`;
        el.style.maxWidth = 'none';
        el.style.maxHeight = 'none';
        el.style.margin = '0';
        return;
      }

      if (key === 'leftEventsContainer' || key === 'headerRightPanel') {
        el.style.position = 'fixed';
      }

      el.style.left = `${left}px`;
      el.style.top = `${top}px`;
      el.style.width = `${(item.widthPercent / 100) * viewportW}px`;
      el.style.height = `${(item.heightPercent / 100) * viewportH}px`;
      if (key === 'nameInput' || key === 'activePetBtn' || key === 'playBtn' || key === 'actionButtons') {
        el.style.maxWidth = 'none';
      }
    });
  }

  async function loadPublicMainMenuLayout() {
    try {
      const res = await fetch('/api/public/config', { cache: 'no-store' });
      const data = await res.json();
      if (data && data.config && data.config.mainMenuLayout) {
        localStorage.setItem('fb_main_menu_layout', JSON.stringify(data.config.mainMenuLayout));
        applyMainMenuLayoutOnPublicPage(data.config.mainMenuLayout);
        const viewport = document.getElementById('layout-editor-viewport');
        if (viewport) renderMainMenuLayoutEditor(data.config.mainMenuLayout);
      }
    } catch (_) {}
  }

  function initMainMenuLayoutEditor() {
    const editor = document.getElementById('layout-editor-viewport');
    if (!editor) return;

    const saved = (window.__fbMainMenuLayout && typeof window.__fbMainMenuLayout === 'object') ? window.__fbMainMenuLayout : null;
    mainMenuLayoutEditor.layoutCache.portrait = resolveLayoutForMode(saved && saved.portrait ? saved : getLayoutEditorDefaults('portrait'), 'portrait');
    mainMenuLayoutEditor.layoutCache.landscape = resolveLayoutForMode(saved && saved.landscape ? saved : getLayoutEditorDefaults('landscape'), 'landscape');
    const initialMode = getCurrentLayoutMode();
    mainMenuLayoutEditor.orientation = initialMode;
    renderMainMenuLayoutEditor(mainMenuLayoutEditor.layoutCache, initialMode);

    document.querySelectorAll('.mode-btn').forEach((btn) => {
      btn.addEventListener('click', () => {
        const nextMode = btn.dataset.layoutMode;
        if (!nextMode) return;
        mainMenuLayoutEditor.orientation = nextMode;
        renderMainMenuLayoutEditor(mainMenuLayoutEditor.layoutCache, nextMode);
      });
    });

    const fullscreenBtn = document.getElementById('toggle-layout-fullscreen-btn');
    if (fullscreenBtn) {
      fullscreenBtn.addEventListener('click', () => {
        const panel = document.querySelector('.layout-editor-panel');
        if (!panel) return;
        const isOpen = panel.classList.contains('is-fullscreen');
        setLayoutEditorFullscreen(!isOpen);
      });
    }

    document.addEventListener('keydown', (event) => {
      if (event.key === 'Escape' && document.querySelector('.layout-editor-panel.is-fullscreen')) {
        setLayoutEditorFullscreen(false);
      }
    });

    const saveBtn = document.getElementById('save-layout-btn');
    if (saveBtn) {
      saveBtn.addEventListener('click', () => {
        const layout = setEditorLayoutFromPage();
        renderMainMenuLayoutEditor(layout, mainMenuLayoutEditor.orientation);
        saveAndApplyMainMenuLayout();
      });
    }

    const resetBtn = document.getElementById('reset-layout-btn');
    if (resetBtn) {
      resetBtn.addEventListener('click', () => {
        mainMenuLayoutEditor.layoutCache.portrait = sanitizeMainMenuLayout(getLayoutEditorDefaults('portrait'));
        mainMenuLayoutEditor.layoutCache.landscape = sanitizeMainMenuLayout(getLayoutEditorDefaults('landscape'));
        renderMainMenuLayoutEditor(mainMenuLayoutEditor.layoutCache, mainMenuLayoutEditor.orientation);
        setLayoutEditorFullscreen(false);
        saveAndApplyMainMenuLayout();
      });
    }
  }

  setTimeout(() => initMainMenuLayoutEditor(), 120);

  // ── Quick World Toggles ────────────────────────────────────────
  $('#quick-maintenance-toggle').addEventListener('change', async (e) => {
    sfx.click();
    try {
      await api('/api/owner/config', {
        method: 'POST',
        body: JSON.stringify({ maintenance: e.target.checked })
      });
      showToast(e.target.checked ? '🛑 Bakım modu açıldı!' : '✅ Bakım modu kapatıldı.');
      loadDashboard();
    } catch (err) {
      showToast(err.message, 'error');
      e.target.checked = !e.target.checked;
    }
  });

  $('#quick-pvp-toggle').addEventListener('change', async (e) => {
    sfx.click();
    try {
      await api('/api/owner/config', {
        method: 'POST',
        body: JSON.stringify({ pvpEnabled: e.target.checked })
      });
      showToast(e.target.checked ? '⚔️ PvP modu açıldı.' : '🕊️ PvP modu kapatıldı.');
      loadDashboard();
    } catch (err) {
      showToast(err.message, 'error');
      e.target.checked = !e.target.checked;
    }
  });

  // ── Quick Broadcast Launcher ───────────────────────────────────
  let quickCategory = 'info';
  $$('.cat-pill').forEach(btn => {
    btn.addEventListener('click', () => {
      sfx.click();
      $$('.cat-pill').forEach(b => b.classList.toggle('active', b === btn));
      quickCategory = btn.dataset.level;
      updateQuickPreview();
    });
  });

  $('#quick-announce-title').addEventListener('input', updateQuickPreview);
  $('#quick-announce-msg').addEventListener('input', (e) => {
    $('#quick-char-count').textContent = e.target.value.length;
    updateQuickPreview();
  });

  function updateQuickPreview() {
    const title = $('#quick-announce-title').value.trim() || 'FORESTBRAWL DUYURUSU';
    const msg = $('#quick-announce-msg').value.trim() || 'Duyuru metni burada canlı görünecek...';
    
    const banner = $('#live-preview-banner');
    banner.className = `preview-banner preview-level-${quickCategory}`;
    
    $('#preview-title').textContent = title.toUpperCase();
    $('#preview-message').textContent = msg;

    const iconMap = { info: '📢', event: '🔥', warning: '⚠️', reward: '🎁' };
    const tagMap = { info: 'DUYURU', event: 'ETKİNLİK', warning: 'UYARI', reward: 'ÖDÜL' };
    $('#preview-icon').textContent = iconMap[quickCategory] || '📢';
    $('#preview-tag').textContent = tagMap[quickCategory] || 'DUYURU';
  }

  $('#quick-send-announce-btn').addEventListener('click', async () => {
    const message = $('#quick-announce-msg').value.trim();
    const title = $('#quick-announce-title').value.trim() || 'FORESTBRAWL DUYURUSU';

    if (!message) {
      showToast('Lütfen bir duyuru mesajı yazın.', 'warning');
      return;
    }

    try {
      await api('/api/owner/announce', {
        method: 'POST',
        body: JSON.stringify({
          message,
          title,
          level: quickCategory,
          sound: 'bell',
          durationMs: 3000
        })
      });
      sfx.gong();
      showToast('🚀 Duyuru tüm sunucuya başarıyla yayınlandı!');
      $('#quick-announce-msg').value = '';
      $('#quick-char-count').textContent = '0';
      updateQuickPreview();
      loadDashboard();
    } catch (err) {
      showToast(err.message, 'error');
    }
  });

  $('#quick-clear-announce-btn').addEventListener('click', async () => {
    sfx.click();
    try {
      await api('/api/owner/announce', {
        method: 'POST',
        body: JSON.stringify({ clear: true })
      });
      showToast('Yayındaki duyuru temizlendi.');
      loadDashboard();
    } catch (err) {
      showToast(err.message, 'error');
    }
  });

  $('#hero-broadcast-trigger').addEventListener('click', () => {
    sfx.click();
    setActiveTab('broadcast');
  });

  // ── Broadcast Studio ───────────────────────────────────────────
  $$('.preset-chip').forEach(btn => {
    btn.addEventListener('click', () => {
      sfx.click();
      $('#studio-title').value = btn.dataset.title || '';
      $('#studio-message').value = btn.dataset.msg || '';
      $('#studio-category').value = btn.dataset.level || 'info';
      $('#studio-char-count').textContent = $('#studio-message').value.length;
      updateStudioPreview();
    });
  });

  $('#studio-category').addEventListener('change', updateStudioPreview);
  $('#studio-title').addEventListener('input', updateStudioPreview);
  $('#studio-message').addEventListener('input', (e) => {
    $('#studio-char-count').textContent = e.target.value.length;
    updateStudioPreview();
  });

  function updateStudioPreview() {
    const category = $('#studio-category').value;
    const title = $('#studio-title').value.trim() || 'FORESTBRAWL DUYURUSU';
    const msg = $('#studio-message').value.trim() || 'Duyuru metnini yazdıkça burası anlık güncellenir.';

    const banner = $('#studio-preview-banner');
    banner.className = `preview-banner preview-level-${category}`;

    const iconMap = { info: '📢', event: '🔥', warning: '⚠️', reward: '🎁' };
    const tagMap = { info: 'DUYURU', event: 'ETKİNLİK', warning: 'UYARI', reward: 'ÖDÜL' };

    $('#sp-icon').textContent = iconMap[category] || '📢';
    $('#sp-tag').textContent = tagMap[category] || 'DUYURU';
    $('#sp-title').textContent = title.toUpperCase();
    $('#sp-message').textContent = msg;
    $('#kf-preview-text').textContent = `${iconMap[category] || '📢'} ${msg}`;
  }

  $('#studio-broadcast-form').addEventListener('submit', async (e) => {
    e.preventDefault();
    const message = $('#studio-message').value.trim();
    const title = $('#studio-title').value.trim() || 'FORESTBRAWL DUYURUSU';
    const level = $('#studio-category').value;
    const sound = $('#studio-sound').value;

    if (!message) {
      showToast('Duyuru metni boş olamaz.', 'warning');
      return;
    }

    try {
      await api('/api/owner/announce', {
        method: 'POST',
        body: JSON.stringify({ message, title, level, sound })
      });
      sfx.gong();
      showToast('🚀 Duyuru stüdyodan canlı olarak yayınlandı!');
      loadDashboard();
    } catch (err) {
      showToast(err.message, 'error');
    }
  });

  $('#studio-clear-btn').addEventListener('click', async () => {
    sfx.click();
    try {
      await api('/api/owner/announce', {
        method: 'POST',
        body: JSON.stringify({ clear: true })
      });
      showToast('Yayındaki duyuru kaldırıldı.');
      loadDashboard();
    } catch (err) {
      showToast(err.message, 'error');
    }
  });

  // ── Tab 2: Live Players Table & God Mode ────────────────────────
  $('#player-search').addEventListener('input', renderPlayersTable);

  function renderPlayersTable() {
    const list = state.dashboardData?.players || [];
    const query = ($('#player-search')?.value || '').toLowerCase().trim();
    const filtered = list.filter(p => !query || `${p.name} ${p.id} ${p.skin}`.toLowerCase().includes(query));

    $('#player-roster-count').textContent = `${filtered.length} / ${list.length} Oyuncu`;

    const tbody = $('#players-table-body');
    if (filtered.length === 0) {
      tbody.innerHTML = `<tr><td colspan="8" class="text-center muted" style="padding:32px 0;">${list.length === 0 ? 'Şu anda oyunda çevrimiçi oyuncu bulunmuyor.' : 'Aramayla eşleşen oyuncu bulunamadı.'}</td></tr>`;
      return;
    }

    tbody.innerHTML = filtered.map(p => {
      const maxHp = p.maxHp || 250;
      const hpPct = Math.max(0, Math.min(100, Math.round((p.hp / maxHp) * 100)));
      const isLowHp = hpPct < 30;

      return `
        <tr>
          <td>
            <div class="player-cell">
              <div class="player-avatar" title="${escapeHtml(p.skin)}">${skinEmoji(p.skin)}</div>
              <div class="player-name-wrap">
                <span class="p-name">${escapeHtml(p.name)}</span>
                <span class="p-id">${p.id}</span>
              </div>
            </div>
          </td>
          <td>
            <span class="pill-state ${p.frozen ? 'frozen' : 'active'}">
              ${p.frozen ? '❄️ Dondurulmuş' : '● Canlı'}
            </span>
          </td>
          <td>
            <div><b>${p.hp}</b> / ${maxHp}</div>
            <div class="hp-bar-wrap">
              <div class="hp-bar-fill ${isLowHp ? 'low' : ''}" style="width:${hpPct}%"></div>
            </div>
          </td>
          <td><b>${Number(p.score || 0).toLocaleString('tr-TR')}</b></td>
          <td><span style="color:var(--amber-light);font-weight:700;">🪙 ${Number(p.gold || 0).toLocaleString('tr-TR')}</span></td>
          <td><b>⚔️ ${p.kills || 0}</b></td>
          <td><code style="font-family:var(--font-mono);font-size:11px;color:var(--text-dim);">${p.x}, ${p.y}</code></td>
          <td class="text-right">
            <div class="actions-cell">
              <button class="btn-action-pill" data-godmode-id="${p.id}" title="God Mode İşlemleri">
                ⚡ God Mode
              </button>
              <button class="btn-action-pill" data-quick-action="heal" data-target-id="${p.id}" title="Can Doldur">
                💚
              </button>
              <button class="btn-action-pill danger" data-quick-action="kick" data-target-id="${p.id}" title="Sunucudan At">
                🚪
              </button>
            </div>
          </td>
        </tr>
      `;
    }).join('');
  }

  function skinEmoji(skin) {
    if (!skin) return '👤';
    if (skin === 'thor') return '⚡';
    if (skin === 'wolf') return '🐺';
    if (skin === 'bear') return '🐻';
    if (skin === 'fox') return '🦊';
    if (skin === 'dragon') return '🐲';
    return '👤';
  }

  // Quick Table Actions
  $('#players-table-body').addEventListener('click', async (e) => {
    const gmBtn = e.target.closest('[data-godmode-id]');
    if (gmBtn) {
      sfx.click();
      openGodModeModal(gmBtn.dataset.godmodeId);
      return;
    }

    const quickBtn = e.target.closest('[data-quick-action]');
    if (quickBtn) {
      sfx.click();
      const action = quickBtn.dataset.quickAction;
      const playerId = quickBtn.dataset.targetId;
      try {
        await api('/api/owner/player-action', {
          method: 'POST',
          body: JSON.stringify({ playerId, action })
        });
        showToast(`Oyuncu işlemi başarılı: ${action}`);
        loadDashboard();
      } catch (err) {
        showToast(err.message, 'error');
      }
    }
  });

  // ── God Mode Modal ─────────────────────────────────────────────
  function openGodModeModal(playerId) {
    const player = (state.dashboardData?.players || []).find(p => p.id === playerId);
    if (!player) {
      showToast('Oyuncu bulunamadı (ayrılmış olabilir).', 'warning');
      return;
    }

    state.selectedPlayer = player;
    $('#gm-player-name').textContent = player.name;
    $('#gm-player-id').textContent = `Socket ID: ${player.id} · Skin: ${player.skin}`;
    $('#gm-hp').textContent = `${player.hp}/${player.maxHp || 250}`;
    $('#gm-score').textContent = Number(player.score || 0).toLocaleString('tr-TR');
    $('#gm-gold').textContent = Number(player.gold || 0).toLocaleString('tr-TR');
    $('#gm-kills').textContent = player.kills || 0;
    $('#gm-pos').textContent = `${player.x}, ${player.y}`;

    const freezeBtn = $('[data-action="toggle_freeze"]');
    if (freezeBtn) {
      $('#gm-freeze-label').textContent = player.frozen ? 'Buzu Çöz (Unfreeze)' : 'Dondur / Sabitle';
    }

    $('#godmode-modal').classList.remove('hidden');
  }

  function closeGodModeModal() {
    $('#godmode-modal').classList.add('hidden');
    state.selectedPlayer = null;
  }

  $('[data-close-modal="godmode"]').addEventListener('click', () => {
    sfx.click();
    closeGodModeModal();
  });

  // Handle God Mode Modal Clicks
  $('.gm-actions-grid').addEventListener('click', async (e) => {
    const btn = e.target.closest('.gm-btn');
    if (!btn || !state.selectedPlayer) return;

    sfx.click();
    const action = btn.dataset.action;
    const playerId = state.selectedPlayer.id;
    let finalAction = action;

    if (action === 'toggle_freeze') {
      finalAction = state.selectedPlayer.frozen ? 'unfreeze' : 'freeze';
    }

    const payload = {
      playerId,
      action: finalAction,
      amount: btn.dataset.amount ? Number(btn.dataset.amount) : undefined,
      x: btn.dataset.x ? Number(btn.dataset.x) : undefined,
      y: btn.dataset.y ? Number(btn.dataset.y) : undefined
    };

    if (finalAction === 'ban') {
      if (!confirm(`${state.selectedPlayer.name} isimli oyuncuyu ve IP adresini sunucudan kalıcı olarak YASAKLAMAK istediğine emin misin?`)) {
        return;
      }
    }

    try {
      await api('/api/owner/player-action', {
        method: 'POST',
        body: JSON.stringify(payload)
      });
      showToast(`İşlem uygulandı: ${finalAction}`);
      closeGodModeModal();
      loadDashboard();
    } catch (err) {
      showToast(err.message, 'error');
    }
  });

  // ── Tab 4: World & Server Configuration ────────────────────────
  ['xprate', 'mobrate', 'resrate'].forEach(id => {
    $(`#cfg-${id}`).addEventListener('input', (e) => {
      $(`#cfg-${id}-val`).textContent = `${Number(e.target.value).toFixed(1)}x`;
    });
  });

  $('#save-world-config-btn').addEventListener('click', async () => {
    sfx.click();
    const payload = {
      maintenance: $('#cfg-maintenance').checked,
      pvpEnabled: $('#cfg-pvp').checked,
      xpRate: Number($('#cfg-xprate').value),
      mobSpawnMultiplier: Number($('#cfg-mobrate').value),
      resourceRespawnMultiplier: Number($('#cfg-resrate').value),
      mainMenuLayout: buildMainMenuLayoutPayload()
    };

    try {
      await api('/api/owner/config', {
        method: 'POST',
        body: JSON.stringify(payload)
      });
      showToast('💾 Dünya ayarları kaydedildi ve tüm haritaya canlı uygulandı!');
      loadDashboard();
    } catch (err) {
      showToast(err.message, 'error');
    }
  });

  function setupMainMenuLayoutEditor() {
    const layoutEditor = document.getElementById('layout-editor');
    if (!layoutEditor) return;

    const editorSections = [
      '#left-events-container',
      '#header-right-panel',
      '#main-menu',
      '#name-input',
      '#active-pet-btn',
      '#play-btn',
      '.grid.grid-cols-2.gap-2.w-full.mt-2.mb-3'
    ];

    editorSections.forEach((selector) => {
      const el = document.querySelector(selector);
      if (!el) return;
      el.setAttribute('data-layout-key', selector.replace(/[#.]/g, ''));
      el.style.touchAction = 'none';
    });
  }

  // ── Tab 5: Registered User Accounts & Moderation ───────────────
  $('#user-search').addEventListener('input', (e) => {
    clearTimeout(state.userSearchTimeout);
    state.userSearchTimeout = setTimeout(() => {
      loadUsers(e.target.value);
    }, 300);
  });

  async function loadUsers(query = '') {
    try {
      const q = encodeURIComponent(query.trim());
      const data = await api(`/api/owner/users?q=${q}`);
      state.usersList = data.users || [];
      renderUsersTable(state.usersList);
    } catch (err) {
      showToast(err.message, 'error');
    }
  }

  function renderUsersTable(users) {
    $('#user-total-count').textContent = `${users.length} Kayıtlı Hesap`;
    const tbody = $('#users-table-body');

    if (users.length === 0) {
      tbody.innerHTML = `<tr><td colspan="8" class="text-center muted" style="padding:32px 0;">Kayıtlı kullanıcı bulunamadı.</td></tr>`;
      return;
    }

    tbody.innerHTML = users.map(u => {
      const kd = (u.deaths > 0 ? (u.kills / u.deaths).toFixed(2) : u.kills || 0);
      return `
        <tr>
          <td>
            <div style="display:flex;align-items:center;gap:10px;">
              <div class="player-avatar">👤</div>
              <div>
                <b style="color:#fff;">${escapeHtml(u.username)}</b>
                <div style="font-family:var(--font-mono);font-size:10px;color:var(--text-dim);">ID: #${u.id}</div>
              </div>
            </div>
          </td>
          <td><span style="font-family:var(--font-mono);font-size:12px;color:var(--text-muted);">${escapeHtml(u.email || '-')}</span></td>
          <td><span style="color:var(--emerald-light);font-weight:700;">⭐ ${Number(u.xp || 0).toLocaleString('tr-TR')}</span></td>
          <td><span style="color:var(--amber-light);font-weight:700;">🪙 ${Number(u.coins || 0).toLocaleString('tr-TR')}</span></td>
          <td><b>${kd}</b> <small class="muted">(${u.kills}/${u.deaths})</small></td>
          <td>${u.gamesPlayed || 0} maç</td>
          <td><b>${Number(u.bestScore || 0).toLocaleString('tr-TR')}</b></td>
          <td class="text-right">
            <button class="btn-action-pill" data-edit-user-id="${u.id}" title="Hesabı Düzenle">
              ✏️ Düzenle
            </button>
          </td>
        </tr>
      `;
    }).join('');
  }

  $('#users-table-body').addEventListener('click', (e) => {
    const btn = e.target.closest('[data-edit-user-id]');
    if (!btn) return;
    sfx.click();
    const userId = Number(btn.dataset.editUserId);
    const user = state.usersList.find(u => u.id === userId);
    if (user) openUserEditModal(user);
  });

  function openUserEditModal(user) {
    $('#ue-user-id').value = user.id;
    $('#ue-user-name').value = user.username;
    $('#ue-username').textContent = user.username;
    $('#ue-id').textContent = `ID: #${user.id} · E-posta: ${user.email || 'Yok'}`;
    $('#ue-coins').value = user.coins || 0;
    $('#ue-xp').value = user.xp || 0;
    $('#ue-new-password').value = '';

    $('#user-edit-modal').classList.remove('hidden');
  }

  function closeUserEditModal() {
    $('#user-edit-modal').classList.add('hidden');
  }

  $('[data-close-modal="user-edit"]').addEventListener('click', () => {
    sfx.click();
    closeUserEditModal();
  });

  $('#user-edit-form').addEventListener('submit', async (e) => {
    e.preventDefault();
    sfx.click();

    const userId = Number($('#ue-user-id').value);
    const username = $('#ue-user-name').value;
    const coins = Number($('#ue-coins').value);
    const xp = Number($('#ue-xp').value);
    const password = $('#ue-new-password').value.trim();

    const payload = { userId, username, coins, xp };
    if (password) payload.password = password;

    try {
      await api('/api/owner/user-edit', {
        method: 'POST',
        body: JSON.stringify(payload)
      });
      showToast('Hesap bilgileri başarıyla güncellendi.');
      closeUserEditModal();
      loadUsers($('#user-search').value);
    } catch (err) {
      showToast(err.message, 'error');
    }
  });

  $('#ue-delete-btn').addEventListener('click', async () => {
    const userId = Number($('#ue-user-id').value);
    const username = $('#ue-user-name').value;

    if (!confirm(`DİKKAT: "${username}" kullanıcısının hesabı ve tüm ilerlemesi kalıcı olarak silinecek. Onaylıyor musun?`)) {
      return;
    }

    try {
      await api('/api/owner/user-edit', {
        method: 'POST',
        body: JSON.stringify({ userId, username, action: 'delete' })
      });
      showToast('Kullanıcı hesabı tamamen silindi.');
      closeUserEditModal();
      loadUsers($('#user-search').value);
    } catch (err) {
      showToast(err.message, 'error');
    }
  });

  // ── Tab 6: Cosmetics Catalog ───────────────────────────────────
  let activeCosmeticType = 'all';
  $$('.cat-filter-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      sfx.click();
      $$('.cat-filter-btn').forEach(b => b.classList.toggle('active', b === btn));
      activeCosmeticType = btn.dataset.type;
      renderCosmeticsGallery();
    });
  });

  async function loadCosmetics() {
    try {
      const data = await api('/api/owner/cosmetics');
      state.cosmeticsData = data;
      renderCosmeticsGallery();
      if (state.selectedCosmeticId) {
        const selected = (data.items || []).find(item => item.id === state.selectedCosmeticId);
        if (selected) fillCosmeticEditor(selected);
      }
    } catch (err) {
      showToast(err.message, 'error');
    }
  }

  state.selectedCosmeticId = null;

  function fillCosmeticEditor(item) {
    const idInput = $('#cosmetic-editor-id');
    const nameInput = $('#cosmetic-editor-name');
    const typeInput = $('#cosmetic-editor-type');
    const rarityInput = $('#cosmetic-editor-rarity');
    const priceInput = $('#cosmetic-editor-price');
    const preview = $('#cosmetic-editor-preview');
    const meta = $('#cosmetic-editor-meta');

    if (!item) {
      if (idInput) idInput.value = '';
      if (nameInput) nameInput.value = '';
      if (typeInput) typeInput.value = 'skin';
      if (rarityInput) rarityInput.value = 'common';
      if (priceInput) priceInput.value = '1000';
      if (preview) preview.removeAttribute('src');
      if (meta) meta.textContent = 'Seçilen kozmetiği düzenlemek için kartı seç.';
      return;
    }

    state.selectedCosmeticId = item.id;
    if (idInput) idInput.value = item.id || '';
    if (nameInput) nameInput.value = item.name || item.id || '';
    if (typeInput) typeInput.value = item.type || 'skin';
    if (rarityInput) rarityInput.value = item.rarity || 'common';
    if (priceInput) priceInput.value = String(Number(item.price || 0));
    if (preview) {
      const assetPath = item.asset ? `../${item.asset}` : '';
      preview.src = assetPath;
      preview.alt = item.name || item.id;
      preview.style.display = assetPath ? 'block' : 'none';
    }
    if (meta) {
      meta.textContent = `${item.type} · ${item.rarity} · ${Number(item.width || 0)} × ${Number(item.height || 0)} px`;
    }
  }

  $('#cosmetic-editor-delete')?.addEventListener('click', async () => {
    const itemId = $('#cosmetic-editor-id')?.value?.trim();
    if (!itemId) return;
    if (!confirm(`${itemId} kozmetiği silinsin mi?`)) return;
    try {
      await api('/api/owner/cosmetics', {
        method: 'DELETE',
        body: JSON.stringify({ id: itemId })
      });
      state.selectedCosmeticId = null;
      fillCosmeticEditor(null);
      await loadCosmetics();
      showToast('Kozmetik silindi ve oyun kataloğundan kaldırıldı.');
    } catch (err) {
      showToast(err.message, 'error');
    }
  });

  $('#cosmetic-editor-form')?.addEventListener('submit', async (event) => {
    event.preventDefault();
    const itemId = $('#cosmetic-editor-id')?.value?.trim();
    if (!itemId) {
      showToast('Önce bir kozmetik seç.', 'error');
      return;
    }

    const selected = (state.cosmeticsData?.items || []).find(item => item.id === itemId) || null;
    const payload = {
      id: itemId,
      name: $('#cosmetic-editor-name')?.value?.trim() || itemId,
      type: $('#cosmetic-editor-type')?.value || selected?.type || 'skin',
      rarity: $('#cosmetic-editor-rarity')?.value || selected?.rarity || 'common',
      price: Number($('#cosmetic-editor-price')?.value || 0),
      asset: selected?.asset || '',
      color: selected?.color || '#b8f36b',
      chests: selected?.chests || []
    };

    try {
      const data = await api('/api/owner/cosmetics', {
        method: 'POST',
        body: JSON.stringify(payload)
      });
      if (data?.item) {
        state.selectedCosmeticId = data.item.id;
        fillCosmeticEditor(data.item);
        await loadCosmetics();
      }
      showToast('Kozmetik kaydedildi ve oyundaki katalog güncellendi.');
    } catch (err) {
      showToast(err.message, 'error');
    }
  });

  let cosmeticUploadData = '';
  const cosmeticUploadForm = $('#cosmetic-upload-form');
  const cosmeticUploadFile = $('#cosmetic-upload-file');
  const cosmeticUploadPreview = $('#cosmetic-upload-preview');
  const cosmeticPreviewStage = $('.cosmetic-preview-stage');
  const cosmeticUploadDimensions = $('#cosmetic-upload-dimensions');
  const cosmeticUploadStatus = $('#cosmetic-upload-status');

  function resetCosmeticUploadForm() {
    cosmeticUploadData = '';
    cosmeticUploadForm?.reset();
    if ($('#cosmetic-upload-price')) $('#cosmetic-upload-price').value = '1000';
    cosmeticUploadPreview?.removeAttribute('src');
    cosmeticPreviewStage?.classList.remove('has-image');
    if (cosmeticUploadDimensions) cosmeticUploadDimensions.textContent = 'Yön ve piksel ölçüsü burada görünür.';
    if (cosmeticUploadStatus) cosmeticUploadStatus.textContent = 'PNG seçtiğinde dosya boyutu ve yön bilgisi burada kontrol edilir.';
  }

  cosmeticUploadFile?.addEventListener('change', () => {
    const file = cosmeticUploadFile.files?.[0];
    if (!file) return;
    if (file.type !== 'image/png') {
      showToast('Yalnızca PNG dosyası yükleyebilirsin.', 'error');
      resetCosmeticUploadForm();
      return;
    }
    if (file.size > 6 * 1024 * 1024) {
      showToast('PNG dosyası en fazla 6 MB olabilir.', 'error');
      resetCosmeticUploadForm();
      return;
    }
    const reader = new FileReader();
    reader.onload = () => {
      const image = new Image();
      image.onload = () => {
        cosmeticUploadData = String(reader.result || '');
        if (cosmeticUploadPreview) cosmeticUploadPreview.src = cosmeticUploadData;
        cosmeticPreviewStage?.classList.add('has-image');
        const orientation = image.naturalWidth === image.naturalHeight ? 'KARE' : image.naturalWidth > image.naturalHeight ? 'YATAY' : 'DİKEY';
        if (cosmeticUploadDimensions) cosmeticUploadDimensions.textContent = `${orientation} · ${image.naturalWidth} × ${image.naturalHeight}px · ${(file.size / 1024 / 1024).toFixed(2)} MB`;
        if (cosmeticUploadStatus) cosmeticUploadStatus.textContent = 'Önizleme hazır. ID, rarity ve fiyatı kontrol edip oyuna yayınlayabilirsin.';
      };
      image.onerror = () => { showToast('PNG önizlemesi okunamadı.', 'error'); resetCosmeticUploadForm(); };
      image.src = String(reader.result || '');
    };
    reader.onerror = () => showToast('PNG dosyası okunamadı.', 'error');
    reader.readAsDataURL(file);
  });

  $('#cosmetic-upload-reset')?.addEventListener('click', resetCosmeticUploadForm);
  cosmeticUploadForm?.addEventListener('submit', async event => {
    event.preventDefault();
    if (!cosmeticUploadData) {
      showToast('Önce bir PNG dosyası seç.', 'error');
      return;
    }
    const submitButton = $('#cosmetic-upload-submit');
    submitButton.disabled = true;
    submitButton.textContent = 'Yükleniyor...';
    try {
      const data = await api('/api/owner/cosmetics/upload', {
        method: 'POST',
        body: JSON.stringify({
          id: $('#cosmetic-upload-id').value.trim(),
          name: $('#cosmetic-upload-name').value.trim(),
          type: $('#cosmetic-upload-type').value,
          rarity: $('#cosmetic-upload-rarity').value,
          price: Number($('#cosmetic-upload-price').value),
          assetData: cosmeticUploadData
        })
      });
      state.cosmeticsData = { ...(state.cosmeticsData || {}), items: data.items || [] };
      renderCosmeticsGallery();
      resetCosmeticUploadForm();
      showToast('PNG oyuna yayınlandı. Tüm oyuncular kataloğu yenilediğinde görecek.');
    } catch (err) {
      showToast(err.message, 'error');
    } finally {
      submitButton.disabled = false;
      submitButton.textContent = "PNG'yi oyuna yayınla";
    }
  });

  async function deleteCosmetic(itemId) {
    if (!confirm(`"${itemId}" kozmetiği ve PNG dosyası silinsin mi?`)) return;
    try {
      const data = await api('/api/owner/cosmetics', { method: 'DELETE', body: JSON.stringify({ id: itemId }) });
      state.cosmeticsData = { ...(state.cosmeticsData || {}), items: data.items || (state.cosmeticsData?.items || []).filter(item => item.id !== itemId) };
      renderCosmeticsGallery();
      showToast('Kozmetik katalogdan ve asset klasöründen silindi.');
    } catch (err) {
      showToast(err.message, 'error');
    }
  }

  function renderCosmeticsGallery() {
    const items = state.cosmeticsData?.items || [];
    const filtered = items.filter(item => activeCosmeticType === 'all' || item.type === activeCosmeticType);

    $('#cosmetic-catalog-count').textContent = `${filtered.length} / ${items.length} Kozmetik`;

    const grid = $('#cosmetics-gallery-grid');
    if (filtered.length === 0) {
      grid.innerHTML = '<div class="empty-feed">Bu kategoride kozmetik bulunamadı.</div>';
      return;
    }

    grid.innerHTML = filtered.map(item => `
      <div class="cosmetic-card" data-cosmetic-id="${escapeHtml(item.id)}">
        <div class="cosmetic-thumb-wrap">
          <img class="cosmetic-img" src="../${item.asset}" onerror="this.outerHTML='🎭'" alt="${escapeHtml(item.name)}">
        </div>
        <div class="cosmetic-name">${escapeHtml(item.name)}</div>
        <span class="cosmetic-rarity-badge rarity-${item.rarity}">${item.rarity}</span>
        <div class="cosmetic-meta">🪙 ${Number(item.price || 0).toLocaleString('tr-TR')} Altın</div>
        <div class="cosmetic-orientation">${String(item.orientation || 'unknown').toUpperCase()} · ${Number(item.width || 0)} × ${Number(item.height || 0)}px</div>
        <div class="cosmetic-upload-actions" style="justify-content: center; margin-top: 12px;">
          <button type="button" class="btn-secondary cosmetic-select-btn" data-cosmetic-id="${escapeHtml(item.id)}">Düzenle</button>
          <button type="button" class="btn-danger cosmetic-delete-btn" data-cosmetic-id="${escapeHtml(item.id)}">Sil</button>
        </div>
      </div>
    `).join('');

    $$('.cosmetic-select-btn', grid).forEach(button => {
      button.addEventListener('click', () => {
        const item = (state.cosmeticsData?.items || []).find(entry => entry.id === button.dataset.cosmeticId);
        if (item) {
          fillCosmeticEditor(item);
          const form = $('#cosmetic-editor-form');
          form?.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
        }
      });
    });

    $$('.cosmetic-delete-btn', grid).forEach(button => button.addEventListener('click', () => deleteCosmetic(button.dataset.cosmeticId)));
  }

  // ── Tab 7: Security & Audit Log Timeline ────────────────────────
  function renderAuditTimeline() {
    const list = state.dashboardData?.audit || [];
    const container = $('#full-audit-timeline');

    if (list.length === 0) {
      container.innerHTML = '<div class="empty-feed">Henüz denetim kaydı bulunmuyor.</div>';
    } else {
      container.innerHTML = list.map(entry => `
        <div class="timeline-entry">
          <div class="timeline-main">
            <span class="timeline-action">${escapeHtml(entry.action)}</span>
            <span class="timeline-actor">Yetkili: ${escapeHtml(entry.username || 'System')}</span>
          </div>
          <div class="timeline-meta">${new Date(entry.at).toLocaleString('tr-TR')}</div>
        </div>
      `).join('');
    }

    // Render Banned Targets
    const banned = state.dashboardData?.banned || [];
    const banContainer = $('#active-ban-list');
    if (banned.length === 0) {
      banContainer.innerHTML = '<div class="empty-feed">Aktif yasaklama bulunmuyor.</div>';
    } else {
      banContainer.innerHTML = banned.map(target => `
        <div class="ban-item">
          <span class="ban-target">🚫 ${escapeHtml(target)}</span>
          <button class="btn-unban" data-unban-target="${escapeHtml(target)}">Yasağı Kaldır</button>
        </div>
      `).join('');
    }
  }

  $('#manual-ban-btn').addEventListener('click', async () => {
    const input = $('#manual-ban-target');
    const target = input.value.trim();
    if (!target) return;

    sfx.click();
    try {
      await api('/api/owner/ban', {
        method: 'POST',
        body: JSON.stringify({ target })
      });
      showToast(`Hedef yasaklandı: ${target}`);
      input.value = '';
      loadDashboard();
    } catch (err) {
      showToast(err.message, 'error');
    }
  });

  $('#active-ban-list').addEventListener('click', async (e) => {
    const btn = e.target.closest('[data-unban-target]');
    if (!btn) return;
    sfx.click();
    const target = btn.dataset.unbanTarget;

    try {
      await api('/api/owner/ban', {
        method: 'POST',
        body: JSON.stringify({ target, action: 'unban' })
      });
      showToast(`Yasak kaldırıldı: ${target}`);
      loadDashboard();
    } catch (err) {
      showToast(err.message, 'error');
    }
  });

  // ── HTML Escape Helper ─────────────────────────────────────────
  function escapeHtml(value) {
    if (value === null || value === undefined) return '';
    return String(value).replace(/[&<>'"]/g, c => ({
      '&': '&amp;',
      '<': '&lt;',
      '>': '&gt;',
      "'": '&#39;',
      '"': '&quot;'
    }[c]));
  }

  // ── Keyboard Shortcuts (ESC closes modals) ────────────────────
  window.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') {
      closeGodModeModal();
      closeUserEditModal();
    }
  });

  // ── Initial Boot ───────────────────────────────────────────────
  (async () => {
    if (!state.token) {
      showLoginView();
      return;
    }

    try {
      const res = await api('/api/owner/me');
      showAppView(res.user);
    } catch (_) {
      showLoginView();
    }
  })();

})();
