(() => {
  'use strict';

  // ============================================================================
  // SABİTLER VE VARSAYILANLAR
  // ============================================================================
  const DB_NAME = 'DepoKutusuDB';
  const DB_VERSION = 1;
  const STORE_NAME = 'appStateStore';
  const STATE_KEY = 'mainState';
  const LS_BACKUP_KEY = 'depokutusu_state_v1';
  const LS_SYNC_CONFIG_KEY = 'depokutusu_sync_config_v1';
  const LS_SECURITY_META_KEY = 'depokutusu_security_meta_v1';
  const PBKDF2_ITERATIONS = 250000;
  const SAFE_MARGIN = 22;
  const DEFAULT_BOX_COUNT = 8;

  const BOX_COLORS = [
    '#4F46E5', // İndigo
    '#0284C7', // Okyanus
    '#059669', // Zümrüt
    '#D97706', // Kehribar
    '#7C3AED', // Mor
    '#DB2777', // Pembe
    '#DC2626', // Mercan
    '#0D9488'  // Turkuaz
  ];

  const SVG_EDIT = '<svg class="svg-icon-sm" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M17 3a2.85 2.83 0 1 1 4 4L7.5 20.5 2 22l1.5-5.5Z"/></svg>';
  const SVG_TRASH = '<svg class="svg-icon-sm" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M3 6h18"/><path d="M19 6v14c0 1-1 2-2 2H7c-1 0-2-1-2-2V6"/><path d="M8 6V4c0-1 1-2 2-2h4c1 0 2 1 2 2v2"/></svg>';
  const SVG_COPY = '<svg class="svg-icon-sm" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect width="14" height="14" x="8" y="8" rx="2" ry="2"/><path d="M4 16c-1.1 0-2-.9-2-2V4c0-1.1.9-2 2-2h10c1.1 0 2 .9 2 2"/></svg>';
  const SVG_OPEN = '<svg class="svg-icon-sm" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M2 3h6a4 4 0 0 1 4 4v14a3 3 0 0 0-3-3H2z"/><path d="M22 3h-6a4 4 0 0 0-4 4v14a3 3 0 0 1 3-3h7z"/></svg>';

  // ============================================================================
  // UYGULAMA DURUMU (STATE) & GÜVENLİK OTURUMU
  // ============================================================================
  let appState = null;
  let securityMeta = loadSecurityMeta();
  let sessionMasterPassword = null; // Asla diske yazılmaz, sadece RAM'de tutulur
  let isVaultLocked = false;
  let lockedLocalEnvelope = null;
  let lockedSyncEnvelope = null;
  let pendingRemoteEnvelope = null;
  let autoLockTimer = null;
  let failedUnlockAttempts = 0;
  let lockoutUntil = 0;
  let syncConfig = loadSyncConfigRaw();
  let activeBoxId = null;
  let editingBoxId = null; // null => yeni kutu oluşturma, string => düzenleme
  let editingParaContext = null; // { boxId, paraId }
  let deferredInstallPrompt = null;
  let cloudPushTimer = null;
  let cloudPullInterval = null;
  let isSyncing = false;
  let activeMobileCorner = 'all';

  // ============================================================================
  // WEB CRYPTO API (AES-256-GCM + PBKDF2-SHA256 E2EE)
  // ============================================================================
  const VaultCrypto = {
    bufToBase64(buf) {
      const bytes = buf instanceof Uint8Array ? buf : new Uint8Array(buf);
      let bin = '';
      const chunk = 0x8000;
      for (let i = 0; i < bytes.length; i += chunk) {
        bin += String.fromCharCode(...bytes.subarray(i, i + chunk));
      }
      return btoa(bin);
    },
    base64ToBuf(b64) {
      const bin = atob(b64);
      const bytes = new Uint8Array(bin.length);
      for (let i = 0; i < bin.length; i += 1) {
        bytes[i] = bin.charCodeAt(i);
      }
      return bytes;
    },
    isEncryptedEnvelope(obj) {
      return Boolean(
        obj &&
        typeof obj === 'object' &&
        obj.e2ee === true &&
        obj.alg === 'AES-256-GCM' &&
        typeof obj.salt === 'string' &&
        typeof obj.iv === 'string' &&
        typeof obj.cipher === 'string'
      );
    },
    async deriveAesKey(password, saltBytes, iterations = PBKDF2_ITERATIONS) {
      if (!window.crypto || !window.crypto.subtle) {
        throw new Error('Bu tarayıcı ortamında Web Crypto API (HTTPS/Güvenli Bağlam) desteklenmiyor.');
      }
      const keyMaterial = await window.crypto.subtle.importKey(
        'raw',
        new TextEncoder().encode(password),
        'PBKDF2',
        false,
        ['deriveKey']
      );
      return window.crypto.subtle.deriveKey(
        {
          name: 'PBKDF2',
          salt: saltBytes,
          iterations,
          hash: 'SHA-256'
        },
        keyMaterial,
        { name: 'AES-GCM', length: 256 },
        false,
        ['encrypt', 'decrypt']
      );
    },
    async encryptPayload(plainObj, password) {
      const salt = window.crypto.getRandomValues(new Uint8Array(16));
      const iv = window.crypto.getRandomValues(new Uint8Array(12));
      const key = await this.deriveAesKey(password, salt, PBKDF2_ITERATIONS);
      const encoded = new TextEncoder().encode(JSON.stringify(plainObj));
      const encrypted = await window.crypto.subtle.encrypt(
        { name: 'AES-GCM', iv },
        key,
        encoded
      );
      return {
        e2ee: true,
        v: 1,
        alg: 'AES-256-GCM',
        kdf: 'PBKDF2-SHA256',
        iter: PBKDF2_ITERATIONS,
        salt: this.bufToBase64(salt),
        iv: this.bufToBase64(iv),
        cipher: this.bufToBase64(encrypted)
      };
    },
    async decryptPayload(envelope, password) {
      const salt = this.base64ToBuf(envelope.salt);
      const iv = this.base64ToBuf(envelope.iv);
      const cipher = this.base64ToBuf(envelope.cipher);
      const key = await this.deriveAesKey(password, salt, Number(envelope.iter) || PBKDF2_ITERATIONS);
      const decrypted = await window.crypto.subtle.decrypt(
        { name: 'AES-GCM', iv },
        key,
        cipher
      );
      return JSON.parse(new TextDecoder().decode(decrypted));
    }
  };

  function loadSecurityMeta() {
    try {
      const raw = localStorage.getItem(LS_SECURITY_META_KEY);
      if (!raw) return { enabled: false, autoLockMinutes: 5 };
      const parsed = JSON.parse(raw);
      return {
        enabled: Boolean(parsed.enabled),
        autoLockMinutes: Number.isFinite(Number(parsed.autoLockMinutes)) ? Number(parsed.autoLockMinutes) : 5
      };
    } catch {
      return { enabled: false, autoLockMinutes: 5 };
    }
  }

  function saveSecurityMeta(meta) {
    securityMeta = {
      enabled: Boolean(meta.enabled),
      autoLockMinutes: Number.isFinite(Number(meta.autoLockMinutes)) ? Number(meta.autoLockMinutes) : 5
    };
    localStorage.setItem(LS_SECURITY_META_KEY, JSON.stringify(securityMeta));
    updateSecurityUI();
  }

  // ============================================================================
  // YARDIMCI FONKSİYONLAR
  // ============================================================================
  const $ = (id) => document.getElementById(id);

  function uid(prefix = 'id') {
    if (typeof crypto !== 'undefined' && crypto.randomUUID) {
      return `${prefix}-${crypto.randomUUID().slice(0, 8)}`;
    }
    return `${prefix}-${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 7)}`;
  }

  function formatDate(ts) {
    if (!ts) return '';
    try {
      return new Intl.DateTimeFormat('tr-TR', {
        day: '2-digit',
        month: 'short',
        hour: '2-digit',
        minute: '2-digit'
      }).format(new Date(ts));
    } catch {
      return '';
    }
  }

  function escapeHtml(str) {
    return String(str ?? '')
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#39;');
  }

  function normalizeUrl(raw) {
    const trimmed = (raw || '').trim();
    if (!trimmed) return '';
    if (/^https?:\/\//i.test(trimmed) || /^mailto:/i.test(trimmed)) {
      return trimmed;
    }
    return `https://${trimmed}`;
  }

  function extractDomain(url) {
    try {
      return new URL(url).hostname.replace(/^www\./, '');
    } catch {
      return url;
    }
  }

  function toBase64Utf8(str) {
    const bytes = new TextEncoder().encode(str);
    let bin = '';
    bytes.forEach((b) => {
      bin += String.fromCharCode(b);
    });
    return btoa(bin);
  }

  function fromBase64Utf8(b64) {
    const bin = atob(b64);
    const bytes = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i += 1) {
      bytes[i] = bin.charCodeAt(i);
    }
    return new TextDecoder().decode(bytes);
  }

  function showToast(message, type = 'info', duration = 3200) {
    const container = $('toastContainer');
    if (!container) return;
    const toast = document.createElement('div');
    toast.className = `toast ${type}`;
    toast.textContent = message;
    container.appendChild(toast);
    setTimeout(() => {
      toast.style.opacity = '0';
      toast.style.transform = 'translateY(8px)';
      toast.style.transition = 'all 0.2s ease';
      setTimeout(() => toast.remove(), 220);
    }, duration);
  }

  // ============================================================================
  // VARSAYILAN VERİ & MİGRASYON
  // ============================================================================
  function createDefaultCornerPositions() {
    return {
      notes: { x: 20, y: 20, w: 460, h: 360 },
      links: { x: 520, y: 20, w: 460, h: 360 },
      paragraphs: { x: 20, y: 410, w: 460, h: 360 },
      images: { x: 520, y: 410, w: 460, h: 360 }
    };
  }

  function createBox(name, color = BOX_COLORS[0], indexNum = 1) {
    const now = Date.now();
    return {
      id: uid('box'),
      name: name || `Depo ${indexNum}`,
      color,
      createdAt: now,
      updatedAt: now,
      scratchpad: '',
      notes: [],
      links: [],
      paragraphs: [],
      images: [],
      hasCustomCornerPos: false,
      cornerPositions: createDefaultCornerPositions()
    };
  }

  function createInitialState() {
    const now = Date.now();
    const boxes = [];
    for (let i = 1; i <= DEFAULT_BOX_COUNT; i += 1) {
      boxes.push(createBox(`Depo ${i}`, BOX_COLORS[(i - 1) % BOX_COLORS.length], i));
    }
    return {
      version: 1,
      isPristineDefault: true,
      updatedAt: now,
      layoutMode: 'quadrant', // 'quadrant' | 'free'
      boxes
    };
  }

  function sanitizeState(raw) {
    if (!raw || typeof raw !== 'object' || !Array.isArray(raw.boxes)) {
      return createInitialState();
    }
    return {
      version: 1,
      isPristineDefault: Boolean(raw.isPristineDefault),
      updatedAt: Number(raw.updatedAt) || Date.now(),
      layoutMode: raw.layoutMode === 'free' ? 'free' : 'quadrant',
      boxes: raw.boxes.map((b, idx) => ({
        id: b.id || uid('box'),
        name: b.name || `Depo ${idx + 1}`,
        color: b.color || BOX_COLORS[idx % BOX_COLORS.length],
        createdAt: Number(b.createdAt) || Date.now(),
        updatedAt: Number(b.updatedAt) || Date.now(),
        scratchpad: typeof b.scratchpad === 'string' ? b.scratchpad : '',
        notes: Array.isArray(b.notes) ? b.notes : [],
        links: Array.isArray(b.links) ? b.links : [],
        paragraphs: Array.isArray(b.paragraphs) ? b.paragraphs : [],
        images: Array.isArray(b.images) ? b.images : [],
        hasCustomCornerPos: Boolean(b.hasCustomCornerPos),
        cornerPositions: b.cornerPositions || createDefaultCornerPositions()
      }))
    };
  }

  // ============================================================================
  // YEREL DEPOLAMA (IndexedDB + localStorage Yedek)
  // ============================================================================
  function openDatabase() {
    return new Promise((resolve, reject) => {
      if (!('indexedDB' in window)) {
        reject(new Error('IndexedDB desteklenmiyor'));
        return;
      }
      const req = indexedDB.open(DB_NAME, DB_VERSION);
      req.onupgradeneeded = () => {
        const db = req.result;
        if (!db.objectStoreNames.contains(STORE_NAME)) {
          db.createObjectStore(STORE_NAME);
        }
      };
      req.onsuccess = () => resolve(req.result);
      req.onerror = () => reject(req.error);
    });
  }

  async function idbGet(key) {
    const db = await openDatabase();
    return new Promise((resolve, reject) => {
      const tx = db.transaction(STORE_NAME, 'readonly');
      const store = tx.objectStore(STORE_NAME);
      const req = store.get(key);
      req.onsuccess = () => resolve(req.result);
      req.onerror = () => reject(req.error);
    });
  }

  async function idbSet(key, val) {
    const db = await openDatabase();
    return new Promise((resolve, reject) => {
      const tx = db.transaction(STORE_NAME, 'readwrite');
      const store = tx.objectStore(STORE_NAME);
      const req = store.put(val, key);
      req.onsuccess = () => resolve();
      req.onerror = () => reject(req.error);
    });
  }

  async function loadLocalStateRaw() {
    try {
      const fromIdb = await idbGet(STATE_KEY);
      if (fromIdb) return fromIdb;
    } catch (err) {
      console.warn('IndexedDB okuma hatası, localStorage deneniyor:', err);
    }
    try {
      const raw = localStorage.getItem(LS_BACKUP_KEY);
      if (raw) return JSON.parse(raw);
    } catch (err) {
      console.warn('localStorage okuma hatası:', err);
    }
    return null;
  }

  async function persistLocalState(markModified = true) {
    if (isVaultLocked) return;
    if (markModified) {
      appState.isPristineDefault = false;
      appState.updatedAt = Date.now();
    }
    let payloadToStore = appState;
    if (sessionMasterPassword) {
      try {
        payloadToStore = await VaultCrypto.encryptPayload(appState, sessionMasterPassword);
      } catch (err) {
        console.error('Yerel şifreleme hatası:', err);
        showToast(`Şifreleme hatası: ${err.message}`, 'error');
        return;
      }
    }
    try {
      await idbSet(STATE_KEY, payloadToStore);
    } catch (err) {
      console.warn('IndexedDB yazma hatası:', err);
    }
    try {
      localStorage.setItem(LS_BACKUP_KEY, JSON.stringify(payloadToStore));
    } catch (err) {
      console.warn('localStorage yedek sınırı:', err);
    }
  }

  function saveStateAndSync() {
    if (isVaultLocked) return;
    updateGlobalStatsAndNav();
    persistLocalState(true).then(() => {
      scheduleCloudPush();
    });
  }

  // ============================================================================
  // BULUT & GİTHUB SENKRONİZASYON MOTORU (E2EE DESTEKLİ)
  // ============================================================================
  function loadSyncConfigRaw() {
    try {
      const raw = localStorage.getItem(LS_SYNC_CONFIG_KEY);
      if (!raw) return { mode: 'none' };
      const parsed = JSON.parse(raw);
      if (VaultCrypto.isEncryptedEnvelope(parsed)) {
        lockedSyncEnvelope = parsed;
        return { mode: 'none' };
      }
      return parsed;
    } catch {
      return { mode: 'none' };
    }
  }

  async function saveSyncConfig(cfg) {
    syncConfig = cfg || { mode: 'none' };
    try {
      if (sessionMasterPassword) {
        const encryptedCfg = await VaultCrypto.encryptPayload(syncConfig, sessionMasterPassword);
        localStorage.setItem(LS_SYNC_CONFIG_KEY, JSON.stringify(encryptedCfg));
      } else {
        localStorage.setItem(LS_SYNC_CONFIG_KEY, JSON.stringify(syncConfig));
      }
    } catch (err) {
      console.error('Sync ayarları şifrelenemedi:', err);
    }
    updateSyncStatusUI();
    refreshPairingOutputs();
  }

  function setSyncBadge(status, label) {
    const badge = $('syncStatusBadge');
    const text = $('syncStatusText');
    if (!badge || !text) return;
    badge.className = `sync-badge status-${status}`;
    text.textContent = label;
  }

  function updateSyncStatusUI() {
    if (syncConfig.mode === 'github' && syncConfig.token && syncConfig.gistId) {
      setSyncBadge('synced', sessionMasterPassword ? 'GitHub Şifreli ✓' : 'GitHub Senkron');
    } else if (syncConfig.mode === 'custom' && syncConfig.url) {
      setSyncBadge('synced', sessionMasterPassword ? 'Bulut Şifreli ✓' : 'Bulut Senkron');
    } else {
      setSyncBadge('local', sessionMasterPassword ? 'Şifreli Yerel' : 'Yerel Kayıt');
    }
  }

  function isCloudConfigured() {
    return (
      (syncConfig.mode === 'github' && syncConfig.token && syncConfig.gistId) ||
      (syncConfig.mode === 'custom' && syncConfig.url)
    );
  }

  function scheduleCloudPush() {
    if (!isCloudConfigured() || isVaultLocked) return;
    clearTimeout(cloudPushTimer);
    setSyncBadge('syncing', 'Kaydediliyor...');
    cloudPushTimer = setTimeout(() => {
      pushToCloud(false);
    }, 1400);
  }

  async function githubApi(path, method = 'GET', body = null, token = syncConfig.token) {
    const headers = {
      Accept: 'application/vnd.github+json',
      Authorization: `Bearer ${token}`
    };
    if (body) {
      headers['Content-Type'] = 'application/json';
    }
    const res = await fetch(`https://api.github.com${path}`, {
      method,
      headers,
      body: body ? JSON.stringify(body) : undefined
    });
    if (!res.ok) {
      const msg = await res.text().catch(() => res.statusText);
      throw new Error(`GitHub API (${res.status}): ${msg}`);
    }
    return res.json();
  }

  async function serializeForCloud() {
    if (sessionMasterPassword) {
      const envelope = await VaultCrypto.encryptPayload(appState, sessionMasterPassword);
      return JSON.stringify(envelope);
    }
    return JSON.stringify(appState);
  }

  async function pushToCloud(showSuccessToast = false) {
    if (!isCloudConfigured() || isVaultLocked) return;
    if (isSyncing) return;
    isSyncing = true;
    setSyncBadge('syncing', sessionMasterPassword ? 'Şifreli Gönderiliyor...' : 'Buluta Gönderiliyor...');
    try {
      const payloadStr = await serializeForCloud();
      if (syncConfig.mode === 'github') {
        await githubApi(`/gists/${syncConfig.gistId}`, 'PATCH', {
          description: 'DepoKutusu Senkronizasyon Verisi',
          files: {
            'depokutusu_data.json': {
              content: payloadStr
            }
          }
        });
      } else if (syncConfig.mode === 'custom') {
        const headers = { 'Content-Type': 'application/json' };
        if (syncConfig.authHeader) {
          headers.Authorization = syncConfig.authHeader;
        }
        const res = await fetch(syncConfig.url, {
          method: 'PUT',
          headers,
          body: payloadStr
        });
        if (!res.ok) throw new Error(`HTTP ${res.status}`);
      }
      setSyncBadge(
        'synced',
        sessionMasterPassword ? 'E2EE Bulut ✓' : (syncConfig.mode === 'github' ? 'GitHub Senkron ✓' : 'Bulut Senkron ✓')
      );
      if (showSuccessToast) showToast('Veriler buluta kaydedildi.', 'success');
    } catch (err) {
      console.error('Buluta gönderme hatası:', err);
      setSyncBadge('error', 'Senkron Hatası');
      if (showSuccessToast) showToast(`Senkronizasyon hatası: ${err.message}`, 'error');
    } finally {
      isSyncing = false;
    }
  }

  async function pullFromCloud(forceApply = false, showAlerts = false) {
    if (isVaultLocked) return false;
    if (!isCloudConfigured()) {
      if (showAlerts) showToast('Henüz bulut senkronizasyonu bağlı değil.', 'warn');
      return false;
    }
    if (isSyncing) return false;
    isSyncing = true;
    setSyncBadge('syncing', 'Kontrol Ediliyor...');
    try {
      let remoteRaw = null;
      if (syncConfig.mode === 'github') {
        const gist = await githubApi(`/gists/${syncConfig.gistId}`, 'GET');
        const fileObj = gist.files && gist.files['depokutusu_data.json'];
        if (fileObj) {
          if (fileObj.truncated && fileObj.raw_url) {
            const rawRes = await fetch(fileObj.raw_url);
            remoteRaw = await rawRes.json();
          } else if (fileObj.content) {
            remoteRaw = JSON.parse(fileObj.content);
          }
        }
      } else if (syncConfig.mode === 'custom') {
        const headers = {};
        if (syncConfig.authHeader) {
          headers.Authorization = syncConfig.authHeader;
        }
        const res = await fetch(syncConfig.url, { method: 'GET', headers });
        if (!res.ok) throw new Error(`HTTP ${res.status}`);
        remoteRaw = await res.json();
      }

      if (remoteRaw && VaultCrypto.isEncryptedEnvelope(remoteRaw)) {
        if (!sessionMasterPassword) {
          pendingRemoteEnvelope = remoteRaw;
          isSyncing = false;
          showVaultLockOverlay('Buluttaki veriler AES-256-GCM ile şifreli. Açmak için kasa şifrenizi girin:');
          return false;
        }
        try {
          remoteRaw = await VaultCrypto.decryptPayload(remoteRaw, sessionMasterPassword);
        } catch {
          pendingRemoteEnvelope = remoteRaw;
          isSyncing = false;
          showVaultLockOverlay('Buluttaki veriler farklı bir Kasa Şifresi ile şifrelenmiş. Çözmek için o şifreyi girin:');
          return false;
        }
      }

      if (remoteRaw && Array.isArray(remoteRaw.boxes)) {
        const remoteState = sanitizeState(remoteRaw);
        const shouldTakeRemote =
          forceApply ||
          (appState.isPristineDefault && !remoteState.isPristineDefault) ||
          remoteState.updatedAt > appState.updatedAt;

        if (shouldTakeRemote) {
          appState = remoteState;
          await persistLocalState(false);
          renderAll();
          if (showAlerts) showToast('Diğer cihazdaki güncel veriler çekildi!', 'success');
        } else if (appState.updatedAt > remoteState.updatedAt && !appState.isPristineDefault) {
          isSyncing = false;
          await pushToCloud(false);
          if (showAlerts) showToast('Yerel değişiklikleriniz buluta gönderildi.', 'success');
          return true;
        } else {
          if (showAlerts) showToast('Tüm veriler zaten güncel.', 'success');
        }
      } else {
        isSyncing = false;
        await pushToCloud(false);
        if (showAlerts) showToast('Veriler buluta ilk kez yüklendi.', 'success');
        return true;
      }

      updateSyncStatusUI();
      return true;
    } catch (err) {
      console.error('Buluttan çekme hatası:', err);
      setSyncBadge('error', 'Bağlantı Hatası');
      if (showAlerts) showToast(`Buluttan veri alınamadı: ${err.message}`, 'error');
      return false;
    } finally {
      isSyncing = false;
    }
  }

  async function connectGithubSync() {
    const token = $('ghTokenInput').value.trim();
    let gistId = $('ghGistIdInput').value.trim();
    if (!token) {
      showToast('Lütfen GitHub Personal Access Token girin.', 'warn');
      return;
    }

    setSyncBadge('syncing', 'GitHub Bağlanıyor...');
    try {
      if (!gistId) {
        const contentStr = await serializeForCloud();
        const created = await githubApi('/gists', 'POST', {
          description: 'DepoKutusu Kişisel Senkronizasyon Verisi',
          public: false,
          files: {
            'depokutusu_data.json': {
              content: contentStr
            }
          }
        }, token);
        gistId = created.id;
        $('ghGistIdInput').value = gistId;
        await saveSyncConfig({ mode: 'github', token, gistId });
        showToast('Yeni gizli GitHub bulut deposu oluşturuldu ve bağlandı!', 'success');
      } else {
        await saveSyncConfig({ mode: 'github', token, gistId });
        await pullFromCloud(false, true);
      }
      switchSyncTab('pair');
    } catch (err) {
      setSyncBadge('error', 'Bağlantı Hatası');
      showToast(`GitHub bağlantısı başarısız: ${err.message}`, 'error', 4500);
    }
  }

  async function connectCustomSync() {
    const url = $('customUrlInput').value.trim();
    const authHeader = $('customAuthHeaderInput').value.trim();
    if (!url) {
      showToast('Lütfen geçerli bir Bulut JSON URL adresi girin.', 'warn');
      return;
    }
    await saveSyncConfig({ mode: 'custom', url, authHeader });
    await pullFromCloud(false, true);
    switchSyncTab('pair');
  }

  async function disconnectSync() {
    await saveSyncConfig({ mode: 'none' });
    $('ghTokenInput').value = '';
    $('ghGistIdInput').value = '';
    $('customUrlInput').value = '';
    $('customAuthHeaderInput').value = '';
    showToast('Bulut bağlantısı kesildi. Veriler yerel cihazda saklanmaya devam ediyor.', 'info');
  }

  async function generatePairingCode() {
    if (!isCloudConfigured()) return '';
    if (sessionMasterPassword) {
      const enc = await VaultCrypto.encryptPayload(syncConfig, sessionMasterPassword);
      return `ENC1:${toBase64Utf8(JSON.stringify(enc))}`;
    }
    return toBase64Utf8(JSON.stringify(syncConfig));
  }

  async function refreshPairingOutputs() {
    const notCfg = $('pairNotConfiguredMsg');
    const readyArea = $('pairReadyArea');
    if (!notCfg || !readyArea) return;

    if (!isCloudConfigured()) {
      notCfg.hidden = false;
      readyArea.hidden = true;
      return;
    }
    notCfg.hidden = true;
    readyArea.hidden = false;

    const code = await generatePairingCode();
    const baseUrl = `${window.location.origin}${window.location.pathname}`;
    const pairLink = `${baseUrl}?sync=${encodeURIComponent(code)}`;

    $('pairingCodeOutput').value = code;
    $('pairingLinkOutput').value = pairLink;
  }

  async function applyPairingCode(rawCode) {
    try {
      const cleaned = rawCode.trim();
      if (!cleaned) return false;
      let decoded = null;

      if (cleaned.startsWith('ENC1:')) {
        const envelope = JSON.parse(fromBase64Utf8(cleaned.slice(5)));
        const pass = ($('pairingDecryptPassInput').value || '').trim() || sessionMasterPassword;
        if (!pass) {
          $('pastePairingCodeInput').value = cleaned;
          $('pairingDecryptWrap').hidden = false;
          openSyncModal('pair');
          setTimeout(() => $('pairingDecryptPassInput').focus(), 40);
          showToast('Bu eşleştirme kodu şifrelidir. Lütfen Kasa Şifrenizi girin.', 'warn', 4500);
          return false;
        }
        try {
          decoded = await VaultCrypto.decryptPayload(envelope, pass);
        } catch {
          $('pairingDecryptWrap').hidden = false;
          $('pairingDecryptPassInput').focus();
          showToast('Kasa şifresi hatalı, eşleştirme kodu çözülemedi!', 'error');
          return false;
        }
        sessionMasterPassword = pass;
        saveSecurityMeta({ enabled: true, autoLockMinutes: securityMeta.autoLockMinutes });
        await persistLocalState(false);
        $('pairingDecryptPassInput').value = '';
        $('pairingDecryptWrap').hidden = true;
      } else {
        decoded = JSON.parse(fromBase64Utf8(cleaned));
      }

      if (!decoded || (decoded.mode !== 'github' && decoded.mode !== 'custom')) {
        throw new Error('Geçersiz eşleştirme kodu');
      }
      await saveSyncConfig(decoded);
      if (decoded.mode === 'github') {
        $('ghTokenInput').value = decoded.token || '';
        $('ghGistIdInput').value = decoded.gistId || '';
      } else {
        $('customUrlInput').value = decoded.url || '';
        $('customAuthHeaderInput').value = decoded.authHeader || '';
      }
      await pullFromCloud(true, true);
      showToast('Cihaz başarıyla eşleştirildi ve veriler eşitlendi!', 'success', 4000);
      return true;
    } catch (err) {
      showToast(`Eşleştirme kodu geçersiz: ${err.message}`, 'error');
      return false;
    }
  }

  async function checkUrlPairingParam() {
    const params = new URLSearchParams(window.location.search);
    const code = params.get('sync');
    if (!code) return;
    const cleanUrl = `${window.location.origin}${window.location.pathname}${window.location.hash}`;
    window.history.replaceState({}, document.title, cleanUrl);
    await applyPairingCode(code);
  }

  // ============================================================================
  // KASA KİLİDİ, GÜVENLİK YÖNETİMİ VE OTOMATİK KİLİT
  // ============================================================================
  function updateSecurityUI() {
    const btn = $('btnOpenSecurityModal');
    const navLabel = $('securityNavLabel');
    const lockBtn = $('btnLockVaultNow');
    const banner = $('securityStatusBanner');
    const curGroup = $('vaultCurrentPassGroup');
    const disableBtn = $('btnDisableVaultLock');
    const isEncrypted = Boolean(securityMeta.enabled || sessionMasterPassword);

    if (btn) btn.classList.toggle('encrypted', isEncrypted);
    if (navLabel) navLabel.textContent = isEncrypted ? 'AES-256 ✓' : 'Güvenlik';
    if (lockBtn) lockBtn.hidden = !sessionMasterPassword;
    if (curGroup) curGroup.hidden = !isEncrypted;
    if (disableBtn) disableBtn.hidden = !isEncrypted;

    if (banner) {
      if (isEncrypted) {
        banner.className = 'info-banner secure';
        banner.innerHTML = '<strong>AES-256-GCM Uçtan Uca Şifreleme Aktif:</strong> Verileriniz bu cihazda ve bulutta şifreli olarak korunuyor. Şifreniz hiçbir yere kaydedilmez.';
      } else {
        banner.className = 'info-banner warn';
        banner.innerHTML = '<strong>Henüz Kasa Şifresi Belirlenmedi:</strong> Verilerinizi GitHub Gist ve bu cihazda şifrelemek için aşağıdan bir kasa şifresi oluşturun.';
      }
    }
    if ($('autoLockMinutesSelect')) {
      $('autoLockMinutesSelect').value = String(securityMeta.autoLockMinutes);
    }
    updateSyncStatusUI();
  }

  function showVaultLockOverlay(customMsg = null) {
    isVaultLocked = true;
    clearTimeout(autoLockTimer);
    $('vaultLockOverlay').hidden = false;
    const errEl = $('vaultUnlockError');
    if (customMsg) {
      errEl.textContent = customMsg;
      errEl.hidden = false;
    } else {
      errEl.hidden = true;
    }
    $('vaultUnlockPassInput').value = '';
    setTimeout(() => $('vaultUnlockPassInput').focus(), 40);
  }

  function clearSensitiveMemoryAndDom() {
    sessionMasterPassword = null;
    appState = createInitialState();
    syncConfig = { mode: 'none' };
    activeBoxId = null;

    ['boxesGrid', 'notesList', 'linksList', 'paragraphsList', 'imagesList', 'megaMenuBoxesList', 'footerBoxesLinks'].forEach((id) => {
      if ($(id)) $(id).innerHTML = '';
    });
    if ($('quickScratchpad')) $('quickScratchpad').value = '';
    if ($('ghTokenInput')) $('ghTokenInput').value = '';
    if ($('ghGistIdInput')) $('ghGistIdInput').value = '';
    if ($('customUrlInput')) $('customUrlInput').value = '';
    if ($('customAuthHeaderInput')) $('customAuthHeaderInput').value = '';
    if ($('pairingLinkOutput')) $('pairingLinkOutput').value = '';
    if ($('pairingCodeOutput')) $('pairingCodeOutput').value = '';

    closeLightbox();
    closeBoxEditModal();
    closeParagraphModal();
    closeMegaMenus();
    collapseAllCorners();
    if ($('syncModal')) $('syncModal').hidden = true;
    if ($('securityModal')) $('securityModal').hidden = true;
    if ($('depoView')) $('depoView').hidden = true;
    if ($('homeView')) $('homeView').hidden = false;
  }

  async function lockVaultNow(reasonMsg = null) {
    if (!sessionMasterPassword && !securityMeta.enabled) return;
    clearTimeout(cloudPushTimer);
    cloudPushTimer = null;
    lockedLocalEnvelope = await loadLocalStateRaw();
    loadSyncConfigRaw();
    clearSensitiveMemoryAndDom();
    updateSecurityUI();
    showVaultLockOverlay(reasonMsg);
  }

  function resetAutoLockTimer() {
    clearTimeout(autoLockTimer);
    if (isVaultLocked || !sessionMasterPassword) return;
    const mins = Number(securityMeta.autoLockMinutes);
    if (mins > 0) {
      autoLockTimer = setTimeout(() => {
        lockVaultNow('Hareketsizlik nedeniyle güvenlik için kasa otomatik kilitlendi.');
      }, mins * 60 * 1000);
    }
  }

  function openSecurityModal() {
    updateSecurityUI();
    $('vaultCurrentPassInput').value = '';
    $('vaultNewPassInput').value = '';
    $('vaultConfirmPassInput').value = '';
    $('securityModal').hidden = false;
  }

  // ============================================================================
  // GÖRÜNÜM YÖNETİMİ VE RENDERING
  // ============================================================================
  function getActiveBox() {
    return appState.boxes.find((b) => b.id === activeBoxId) || null;
  }

  function renderAll() {
    renderHomeGrid();
    if (activeBoxId && getActiveBox()) {
      renderDepoView();
    } else if (activeBoxId) {
      closeDepoView();
    }
  }

  function updateGlobalStatsAndNav() {
    let totalNotes = 0;
    let totalLinks = 0;
    let totalMedia = 0;
    appState.boxes.forEach((b) => {
      totalNotes += b.notes.length + (b.scratchpad.trim() ? 1 : 0);
      totalLinks += b.links.length;
      totalMedia += b.paragraphs.length + b.images.length;
    });
    if ($('boxCountBadge')) $('boxCountBadge').textContent = appState.boxes.length;
    if ($('statTotalNotes')) $('statTotalNotes').textContent = totalNotes;
    if ($('statTotalLinks')) $('statTotalLinks').textContent = totalLinks;
    if ($('statTotalMedia')) $('statTotalMedia').textContent = totalMedia;
    if ($('megaMenuTotalCount')) $('megaMenuTotalCount').textContent = `${appState.boxes.length} Depo`;

    const megaList = $('megaMenuBoxesList');
    if (megaList) {
      megaList.innerHTML = '';
      appState.boxes.forEach((box) => {
        const btn = document.createElement('button');
        btn.type = 'button';
        btn.className = 'mega-box-link';
        btn.innerHTML = `
          <span class="mega-box-dot" style="background:${escapeHtml(box.color || '#4F46E5')}"></span>
          <span class="mega-box-name">${escapeHtml(box.name)}</span>
        `;
        btn.addEventListener('click', () => {
          closeMegaMenus();
          openDepoView(box.id);
        });
        megaList.appendChild(btn);
      });
    }

    const footerLinks = $('footerBoxesLinks');
    if (footerLinks) {
      footerLinks.innerHTML = '';
      appState.boxes.slice(0, 5).forEach((box) => {
        const li = document.createElement('li');
        const btn = document.createElement('button');
        btn.type = 'button';
        btn.className = 'footer-link-btn';
        btn.textContent = box.name;
        btn.addEventListener('click', () => openDepoView(box.id));
        li.appendChild(btn);
        footerLinks.appendChild(li);
      });
    }
  }

  function renderHomeGrid() {
    const grid = $('boxesGrid');
    const query = ($('boxSearchInput').value || '').trim().toLowerCase();
    updateGlobalStatsAndNav();

    const filtered = appState.boxes.filter((b) =>
      b.name.toLowerCase().includes(query)
    );

    grid.innerHTML = '';

    filtered.forEach((box, idx) => {
      const noteCount = box.notes.length + (box.scratchpad.trim() ? 1 : 0);
      const linkCount = box.links.length;
      const paraCount = box.paragraphs.length;
      const imgCount = box.images.length;

      const summaryParts = [];
      if (noteCount) summaryParts.push(`${noteCount} not`);
      if (linkCount) summaryParts.push(`${linkCount} link`);
      if (paraCount) summaryParts.push(`${paraCount} yazı`);
      if (imgCount) summaryParts.push(`${imgCount} resim`);
      const summaryText = summaryParts.length ? summaryParts.join(' • ') : 'Boş depo — açmak için tıkla';
      const indexStr = String(idx + 1).padStart(2, '0');

      const card = document.createElement('div');
      card.className = 'box-card';
      card.style.setProperty('--box-accent', box.color || '#4F46E5');
      card.setAttribute('tabindex', '0');
      card.innerHTML = `
        <div class="box-card-top-bar">
          <span class="box-index-tag">${indexStr}</span>
          <div class="box-card-actions">
            <button type="button" class="btn-mini-icon btn-rename-box" title="İsmini / Rengini Düzenle">${SVG_EDIT}</button>
            <button type="button" class="btn-mini-icon danger btn-delete-box" title="Kutucuğu Sil">${SVG_TRASH}</button>
          </div>
        </div>

        <div class="box-plus-center">
          <div class="box-plus-circle" aria-hidden="true">+</div>
        </div>

        <div class="box-card-footer">
          <h3 class="box-card-name">${escapeHtml(box.name)}</h3>
          <p class="box-card-summary">${escapeHtml(summaryText)}</p>
          <div class="box-corner-dots" title="4 Köşe Durumu: Notlar · Linkler · Paragraflar · Resimler">
            <span class="c-dot c-amber ${noteCount ? 'active' : ''}"></span>
            <span class="c-dot c-sky ${linkCount ? 'active' : ''}"></span>
            <span class="c-dot c-emerald ${paraCount ? 'active' : ''}"></span>
            <span class="c-dot c-purple ${imgCount ? 'active' : ''}"></span>
          </div>
        </div>
      `;

      card.addEventListener('click', (e) => {
        if (e.target.closest('.btn-rename-box')) {
          e.stopPropagation();
          openBoxEditModal(box.id);
          return;
        }
        if (e.target.closest('.btn-delete-box')) {
          e.stopPropagation();
          deleteBox(box.id);
          return;
        }
        openDepoView(box.id);
      });

      card.addEventListener('keydown', (e) => {
        if (e.key === 'Enter' || e.key === ' ') {
          e.preventDefault();
          openDepoView(box.id);
        }
      });

      grid.appendChild(card);
    });

    // Izgara sonunda her zaman "+ Daha Fazla Kutucuk Ekle" kartı
    const addCard = document.createElement('button');
    addCard.type = 'button';
    addCard.className = 'box-card box-card-add-new';
    addCard.innerHTML = `
      <div class="plus-big">+</div>
      <span>Daha Fazla Kutucuk Ekle</span>
    `;
    addCard.addEventListener('click', () => openBoxEditModal(null));
    grid.appendChild(addCard);
  }

  function openDepoView(boxId) {
    activeBoxId = boxId;
    const box = getActiveBox();
    if (!box) return;
    $('linkForm').hidden = true;
    $('paragraphForm').hidden = true;
    $('imageUrlForm').hidden = true;
    $('homeView').hidden = true;
    $('depoView').hidden = false;
    window.scrollTo({ top: 0, behavior: 'smooth' });
    renderDepoView();
  }

  function closeDepoView() {
    activeBoxId = null;
    collapseAllCorners();
    $('depoView').hidden = true;
    $('homeView').hidden = false;
    renderHomeGrid();
  }

  function renderDepoView() {
    const box = getActiveBox();
    if (!box) return;

    $('activeBoxTitle').textContent = box.name;
    $('activeBoxColorDot').style.backgroundColor = box.color || '#4F46E5';
    $('centerEmblemTitle').textContent = box.name;
    const emblemDot = document.querySelector('.center-emblem-dot');
    if (emblemDot) emblemDot.style.backgroundColor = box.color || '#4F46E5';

    // Yerleşim modu (4 Köşe vs Serbest Köşe Masası)
    applyLayoutModeUI();

    // Sol Üst: Not Kısmı
    const scratchpad = $('quickScratchpad');
    if (document.activeElement !== scratchpad) {
      scratchpad.value = box.scratchpad || '';
    }
    renderNotesList(box);

    // Sağ Üst: Linkler
    renderLinksList(box);

    // Sol Alt: Paragraflar
    renderParagraphsList(box);

    // Sağ Alt: Resimler
    renderImagesList(box);
  }

  function renderNotesList(box) {
    const list = $('notesList');
    if (!box.notes.length) {
      list.innerHTML = '<li class="empty-placeholder">Henüz maddeli kısa not yok.</li>';
      return;
    }
    list.innerHTML = '';
    box.notes.forEach((note) => {
      const li = document.createElement('li');
      li.className = 'item-card';
      li.innerHTML = `
        <div class="item-card-content">
          <div>${escapeHtml(note.text)}</div>
          <div class="item-meta">${formatDate(note.createdAt)}</div>
        </div>
        <div class="item-card-actions">
          <button type="button" class="btn-mini-icon danger btn-del" title="Sil">${SVG_TRASH}</button>
        </div>
      `;
      li.querySelector('.btn-del').addEventListener('click', () => {
        box.notes = box.notes.filter((n) => n.id !== note.id);
        box.updatedAt = Date.now();
        renderNotesList(box);
        saveStateAndSync();
      });
      list.appendChild(li);
    });
  }

  function renderLinksList(box) {
    const list = $('linksList');
    if (!box.links.length) {
      list.innerHTML = '<li class="empty-placeholder">Bu köşeye henüz link eklenmedi. Yukarıdaki "+ Link Ekle" butonunu kullanabilirsiniz.</li>';
      return;
    }
    list.innerHTML = '';
    box.links.forEach((link) => {
      const domain = extractDomain(link.url);
      const faviconUrl = `https://www.google.com/s2/favicons?domain=${encodeURIComponent(domain)}&sz=64`;
      const li = document.createElement('li');
      li.className = 'item-card';
      li.innerHTML = `
        <div class="item-card-content">
          <div class="link-row-head">
            <img class="link-favicon" src="${escapeHtml(faviconUrl)}" alt="" loading="lazy" />
            <a class="link-anchor" href="${escapeHtml(link.url)}" target="_blank" rel="noopener noreferrer">
              ${escapeHtml(link.title || domain)}
            </a>
          </div>
          <div class="link-url-sub">${escapeHtml(link.url)}</div>
          ${link.desc ? `<div class="link-desc-sub">${escapeHtml(link.desc)}</div>` : ''}
        </div>
        <div class="item-card-actions">
          <button type="button" class="btn-mini-icon btn-copy" title="Linki Kopyala">${SVG_COPY}</button>
          <button type="button" class="btn-mini-icon danger btn-del" title="Sil">${SVG_TRASH}</button>
        </div>
      `;
      li.querySelector('.btn-copy').addEventListener('click', () => {
        navigator.clipboard?.writeText(link.url);
        showToast('Link panoya kopyalandı.', 'success');
      });
      li.querySelector('.btn-del').addEventListener('click', () => {
        box.links = box.links.filter((l) => l.id !== link.id);
        box.updatedAt = Date.now();
        renderLinksList(box);
        saveStateAndSync();
      });
      list.appendChild(li);
    });
  }

  function renderParagraphsList(box) {
    const list = $('paragraphsList');
    if (!box.paragraphs.length) {
      list.innerHTML = '<div class="empty-placeholder">Henüz paragraf eklenmedi. Yukarıdaki "+ Paragraf Yaz" butonuna tıklayın.</div>';
      return;
    }
    list.innerHTML = '';
    box.paragraphs.forEach((para) => {
      const card = document.createElement('div');
      card.className = 'paragraph-card';
      card.innerHTML = `
        <div class="paragraph-card-head">
          <span class="paragraph-card-title">${escapeHtml(para.title || 'Başlıksız Paragraf')}</span>
          <div class="item-card-actions">
            <button type="button" class="btn-mini-icon btn-open" title="Tam Oku / Düzenle">${SVG_OPEN}</button>
            <button type="button" class="btn-mini-icon btn-copy" title="Metni Kopyala">${SVG_COPY}</button>
            <button type="button" class="btn-mini-icon danger btn-del" title="Sil">${SVG_TRASH}</button>
          </div>
        </div>
        <p class="paragraph-card-text">${escapeHtml(para.content)}</p>
        <div class="item-meta">${formatDate(para.createdAt)}</div>
      `;
      card.querySelector('.btn-open').addEventListener('click', () => {
        openParagraphModal(box.id, para.id);
      });
      card.querySelector('.btn-copy').addEventListener('click', () => {
        navigator.clipboard?.writeText(para.content);
        showToast('Paragraf kopyalandı.', 'success');
      });
      card.querySelector('.btn-del').addEventListener('click', () => {
        box.paragraphs = box.paragraphs.filter((p) => p.id !== para.id);
        box.updatedAt = Date.now();
        renderParagraphsList(box);
        saveStateAndSync();
      });
      list.appendChild(card);
    });
  }

  function renderImagesList(box) {
    const grid = $('imagesList');
    if (!box.images.length) {
      grid.innerHTML = '<div class="empty-placeholder" style="grid-column: 1 / -1;">Bu köşede henüz resim yok.</div>';
      return;
    }
    grid.innerHTML = '';
    box.images.forEach((img) => {
      const tile = document.createElement('div');
      tile.className = 'image-tile';
      tile.innerHTML = `
        <img src="${escapeHtml(img.dataUrl)}" alt="${escapeHtml(img.title || 'Depo Resmi')}" loading="lazy" />
        <div class="image-tile-foot">
          <span class="image-tile-title" title="${escapeHtml(img.title || 'Resim')}">${escapeHtml(img.title || 'Resim')}</span>
          <button type="button" class="btn-mini-icon danger btn-del" title="Sil">${SVG_TRASH}</button>
        </div>
      `;
      tile.querySelector('img').addEventListener('click', () => {
        openLightbox(img.dataUrl, img.title || '');
      });
      tile.querySelector('.btn-del').addEventListener('click', () => {
        box.images = box.images.filter((i) => i.id !== img.id);
        box.updatedAt = Date.now();
        renderImagesList(box);
        saveStateAndSync();
      });
      grid.appendChild(tile);
    });
  }

  // ============================================================================
  // KUTUCUK İŞLEMLERİ (EKLE / DÜZENLE / SİL)
  // ============================================================================
  function renderColorSwatches(selectedColor) {
    const wrap = $('boxColorSwatches');
    wrap.innerHTML = '';
    BOX_COLORS.forEach((c) => {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = `swatch-btn ${c === selectedColor ? 'selected' : ''}`;
      btn.style.backgroundColor = c;
      btn.addEventListener('click', () => {
        $('boxColorPicker').value = c;
        wrap.querySelectorAll('.swatch-btn').forEach((el) => el.classList.remove('selected'));
        btn.classList.add('selected');
      });
      wrap.appendChild(btn);
    });
  }

  function openBoxEditModal(boxId) {
    editingBoxId = boxId;
    const isNew = !boxId;
    const box = boxId ? appState.boxes.find((b) => b.id === boxId) : null;
    $('boxEditModalTitle').textContent = isNew ? 'Yeni Depo Kutucuğu Oluştur' : 'Kutucuğu Düzenle';
    $('boxNameInput').value = isNew ? `Depo ${appState.boxes.length + 1}` : box.name;
    const col = isNew ? BOX_COLORS[appState.boxes.length % BOX_COLORS.length] : box.color;
    $('boxColorPicker').value = col;
    renderColorSwatches(col);
    $('boxEditModal').hidden = false;
    setTimeout(() => {
      $('boxNameInput').focus();
      $('boxNameInput').select();
    }, 30);
  }

  function closeBoxEditModal() {
    $('boxEditModal').hidden = true;
    editingBoxId = null;
  }

  function deleteBox(boxId) {
    const box = appState.boxes.find((b) => b.id === boxId);
    if (!box) return;
    if (!window.confirm(`"${box.name}" kutucuğunu ve içindeki tüm verileri silmek istediğinize emin misiniz?`)) {
      return;
    }
    appState.boxes = appState.boxes.filter((b) => b.id !== boxId);
    renderHomeGrid();
    saveStateAndSync();
    showToast(`"${box.name}" silindi.`, 'info');
  }

  // ============================================================================
  // RESİM SIKIŞTIRMA & YÜKLEME
  // ============================================================================
  function compressImageFile(file) {
    return new Promise((resolve, reject) => {
      const reader = new FileReader();
      reader.onerror = () => reject(new Error('Dosya okunamadı'));
      reader.onload = () => {
        const img = new Image();
        img.onerror = () => reject(new Error('Geçersiz görsel dosyası'));
        img.onload = () => {
          const maxDim = 900;
          let { width, height } = img;
          if (width > maxDim || height > maxDim) {
            const ratio = Math.min(maxDim / width, maxDim / height);
            width = Math.round(width * ratio);
            height = Math.round(height * ratio);
          }
          const canvas = document.createElement('canvas');
          canvas.width = width;
          canvas.height = height;
          const ctx = canvas.getContext('2d');
          ctx.drawImage(img, 0, 0, width, height);
          const dataUrl = canvas.toDataURL('image/jpeg', 0.76);
          resolve(dataUrl);
        };
        img.src = reader.result;
      };
      reader.readAsDataURL(file);
    });
  }

  async function handleImageFiles(files) {
    const box = getActiveBox();
    if (!box) return;
    const validFiles = Array.from(files).filter((f) => f.type.startsWith('image/'));
    if (!validFiles.length) {
      showToast('Lütfen geçerli bir resim dosyası seçin.', 'warn');
      return;
    }

    for (const file of validFiles) {
      try {
        const dataUrl = await compressImageFile(file);
        box.images.unshift({
          id: uid('img'),
          title: file.name.replace(/\.[^.]+$/, ''),
          dataUrl,
          createdAt: Date.now()
        });
      } catch (err) {
        showToast(`Resim eklenemedi: ${err.message}`, 'error');
      }
    }

    box.updatedAt = Date.now();
    renderImagesList(box);
    saveStateAndSync();
    showToast(`${validFiles.length} resim eklendi.`, 'success');
  }

  // ============================================================================
  // ÇARPIŞMASIZ SERBEST KÖŞE & KENAR YERLEŞİM ALGORİTMASI
  // ============================================================================
  function getContainerBounds() {
    const container = $('depoCornersContainer');
    return {
      w: Math.max(container.clientWidth, 960),
      h: Math.max(container.clientHeight, 800)
    };
  }

  function clampRect(r, bounds) {
    const w = Math.min(Math.max(r.w, 280), bounds.w - 32);
    const h = Math.min(Math.max(r.h, 240), bounds.h - 32);
    const x = Math.max(16, Math.min(r.x, bounds.w - w - 16));
    const y = Math.max(16, Math.min(r.y, bounds.h - h - 16));
    return { x, y, w, h };
  }

  function resolveCollisions(movedKey, rects, bounds) {
    const keys = Object.keys(rects);
    rects[movedKey] = clampRect(rects[movedKey], bounds);

    // 6 iterasyonlu AABB çarpışma çözücü (hiçbir köşe paneli birbiriyle çakışamaz)
    for (let pass = 0; pass < 6; pass += 1) {
      for (let i = 0; i < keys.length; i += 1) {
        for (let j = i + 1; j < keys.length; j += 1) {
          const kA = keys[i];
          const kB = keys[j];
          // Hareket ettirilen kutu mümkün olduğunca yerinde kalsın, diğeri kaçsın
          const primaryKey = kB === movedKey ? kB : kA;
          const secondaryKey = primaryKey === kA ? kB : kA;

          const a = rects[primaryKey];
          let b = rects[secondaryKey];

          const axCenter = a.x + a.w / 2;
          const ayCenter = a.y + a.h / 2;
          const bxCenter = b.x + b.w / 2;
          const byCenter = b.y + b.h / 2;

          const overlapX = (a.w / 2 + b.w / 2 + SAFE_MARGIN) - Math.abs(axCenter - bxCenter);
          const overlapY = (a.h / 2 + b.h / 2 + SAFE_MARGIN) - Math.abs(ayCenter - byCenter);

          if (overlapX > 0 && overlapY > 0) {
            if (overlapX < overlapY) {
              const dir = bxCenter >= axCenter ? 1 : -1;
              b.x += dir * overlapX;
              b = clampRect(b, bounds);
              // Duvara dayandıysa diğer eksenden kaydır
              const newOverlapX = (a.w / 2 + b.w / 2 + SAFE_MARGIN) - Math.abs((a.x + a.w / 2) - (b.x + b.w / 2));
              if (newOverlapX > 1) {
                const dirY = byCenter >= ayCenter ? 1 : -1;
                b.y += dirY * overlapY;
              }
            } else {
              const dir = byCenter >= ayCenter ? 1 : -1;
              b.y += dir * overlapY;
              b = clampRect(b, bounds);
              const newOverlapY = (a.h / 2 + b.h / 2 + SAFE_MARGIN) - Math.abs((a.y + a.h / 2) - (b.y + b.h / 2));
              if (newOverlapY > 1) {
                const dirX = bxCenter >= axCenter ? 1 : -1;
                b.x += dirX * overlapX;
              }
            }
            rects[secondaryKey] = clampRect(b, bounds);
          }
        }
      }
    }
    return rects;
  }

  function snapCornersSymmetrically(box) {
    const bounds = getContainerBounds();
    const pad = 20;
    const gap = 28;
    const halfW = Math.floor((bounds.w - pad * 2 - gap) / 2);
    const halfH = Math.floor((bounds.h - pad * 2 - gap) / 2);

    box.cornerPositions = {
      notes: { x: pad, y: pad, w: halfW, h: halfH },
      links: { x: pad + halfW + gap, y: pad, w: halfW, h: halfH },
      paragraphs: { x: pad, y: pad + halfH + gap, w: halfW, h: halfH },
      images: { x: pad + halfW + gap, y: pad + halfH + gap, w: halfW, h: halfH }
    };
  }

  function applyFreePositionsToDom(box) {
    const isDesktop = window.innerWidth >= 900;
    const panels = document.querySelectorAll('.corner-panel');
    panels.forEach((panel) => {
      const key = panel.dataset.corner;
      if (appState.layoutMode !== 'free' || !isDesktop) {
        panel.style.left = '';
        panel.style.top = '';
        panel.style.width = '';
        panel.style.height = '';
        return;
      }
      const pos = box.cornerPositions[key];
      if (pos) {
        panel.style.left = `${pos.x}px`;
        panel.style.top = `${pos.y}px`;
        panel.style.width = `${pos.w}px`;
        panel.style.height = `${pos.h}px`;
      }
    });
  }

  function applyLayoutModeUI() {
    const box = getActiveBox();
    const container = $('depoCornersContainer');
    const isFree = appState.layoutMode === 'free';

    container.classList.toggle('layout-free', isFree);
    container.classList.toggle('layout-quadrant', !isFree);
    $('btnSnapCorners').hidden = !isFree;

    document.querySelectorAll('#layoutModeToggle .seg-btn').forEach((btn) => {
      btn.classList.toggle('active', btn.dataset.layout === appState.layoutMode);
    });

    if (box) {
      if (isFree && window.innerWidth >= 900) {
        if (!box.hasCustomCornerPos) {
          snapCornersSymmetrically(box);
        } else {
          const bounds = getContainerBounds();
          resolveCollisions('notes', box.cornerPositions, bounds);
        }
      }
      applyFreePositionsToDom(box);
    }
  }

  function setupFreeCanvasDragAndResize() {
    const container = $('depoCornersContainer');
    let interaction = null; // { type: 'drag'|'resize', cornerKey, startX, startY, origRect }

    container.addEventListener('pointerdown', (e) => {
      if (appState.layoutMode !== 'free' || window.innerWidth < 900) return;
      const box = getActiveBox();
      if (!box) return;

      const resizeEl = e.target.closest('.resize-handle');
      const headerEl = e.target.closest('.drag-handle');
      if (!resizeEl && !headerEl) return;
      if (e.target.closest('button')) return;

      const panel = e.target.closest('.corner-panel');
      if (!panel || panel.classList.contains('expanded')) return;

      const cornerKey = panel.dataset.corner;
      const origRect = { ...box.cornerPositions[cornerKey] };

      panel.classList.add('dragging');
      interaction = {
        type: resizeEl ? 'resize' : 'drag',
        cornerKey,
        startX: e.clientX,
        startY: e.clientY,
        origRect
      };
      e.preventDefault();
    });

    window.addEventListener('pointermove', (e) => {
      if (!interaction) return;
      const box = getActiveBox();
      if (!box) return;

      const dx = e.clientX - interaction.startX;
      const dy = e.clientY - interaction.startY;
      const bounds = getContainerBounds();
      const target = box.cornerPositions[interaction.cornerKey];

      if (interaction.type === 'drag') {
        target.x = interaction.origRect.x + dx;
        target.y = interaction.origRect.y + dy;
      } else {
        target.w = Math.max(280, interaction.origRect.w + dx);
        target.h = Math.max(240, interaction.origRect.h + dy);
      }

      resolveCollisions(interaction.cornerKey, box.cornerPositions, bounds);
      applyFreePositionsToDom(box);
    });

    window.addEventListener('pointerup', () => {
      if (!interaction) return;
      document.querySelectorAll('.corner-panel.dragging').forEach((p) => p.classList.remove('dragging'));
      interaction = null;
      const box = getActiveBox();
      if (box) {
        box.hasCustomCornerPos = true;
        box.updatedAt = Date.now();
        saveStateAndSync();
      }
    });
  }

  function collapseAllCorners() {
    document.querySelectorAll('.corner-panel.expanded').forEach((p) => {
      p.classList.remove('expanded');
      const btn = p.querySelector('.btn-expand-corner');
      if (btn) btn.textContent = '⤢';
    });
  }

  // ============================================================================
  // MODALLAR (PARAGRAF / LIGHTBOX / SYNC)
  // ============================================================================
  function openParagraphModal(boxId, paraId) {
    const box = appState.boxes.find((b) => b.id === boxId);
    if (!box) return;
    const para = box.paragraphs.find((p) => p.id === paraId);
    if (!para) return;
    editingParaContext = { boxId, paraId };
    $('paraModalHeading').textContent = para.title || 'Paragraf';
    $('paraModalTitleInput').value = para.title || '';
    $('paraModalBodyInput').value = para.content || '';
    $('paragraphReadModal').hidden = false;
  }

  function closeParagraphModal() {
    $('paragraphReadModal').hidden = true;
    editingParaContext = null;
  }

  function openLightbox(src, caption) {
    $('lightboxImg').src = src;
    $('lightboxCaption').textContent = caption;
    $('lightboxModal').hidden = false;
  }

  function closeLightbox() {
    $('lightboxModal').hidden = true;
    $('lightboxImg').src = '';
  }

  function switchSyncTab(tabName) {
    document.querySelectorAll('.sync-tab').forEach((btn) => {
      btn.classList.toggle('active', btn.dataset.syncTab === tabName);
    });
    const map = {
      github: 'syncTabGithub',
      pair: 'syncTabPair',
      custom: 'syncTabCustom',
      backup: 'syncTabBackup'
    };
    Object.entries(map).forEach(([key, elId]) => {
      $(elId).hidden = key !== tabName;
    });
    if (tabName === 'pair') {
      refreshPairingOutputs();
    }
  }

  function closeMegaMenus() {
    const boxesBtn = $('navMegaBoxesBtn');
    const boxesPanel = $('navMegaBoxesPanel');
    const cornersBtn = $('navMegaCornersBtn');
    const cornersPanel = $('navMegaCornersPanel');
    if (boxesBtn && boxesPanel) {
      boxesBtn.setAttribute('aria-expanded', 'false');
      boxesPanel.hidden = true;
    }
    if (cornersBtn && cornersPanel) {
      cornersBtn.setAttribute('aria-expanded', 'false');
      cornersPanel.hidden = true;
    }
  }

  function focusCornerPanel(cornerKey) {
    closeMegaMenus();
    if (!activeBoxId || $('depoView').hidden) {
      if (!appState.boxes.length) return;
      openDepoView(appState.boxes[0].id);
    }
    const targetMap = {
      notes: 'cornerNotes',
      links: 'cornerLinks',
      paragraphs: 'cornerParagraphs',
      images: 'cornerImages'
    };
    const panel = $(targetMap[cornerKey]);
    if (panel) {
      panel.scrollIntoView({ behavior: 'smooth', block: 'center' });
      panel.style.boxShadow = '0 0 0 3px rgba(79, 70, 229, 0.35)';
      setTimeout(() => {
        panel.style.boxShadow = '';
      }, 1200);
    }
  }

  function openSyncModal(initialTab = null) {
    if (initialTab) {
      if (syncConfig.mode === 'github') {
        $('ghTokenInput').value = syncConfig.token || '';
        $('ghGistIdInput').value = syncConfig.gistId || '';
      } else if (syncConfig.mode === 'custom') {
        $('customUrlInput').value = syncConfig.url || '';
        $('customAuthHeaderInput').value = syncConfig.authHeader || '';
      }
      switchSyncTab(initialTab);
    } else if (syncConfig.mode === 'github') {
      $('ghTokenInput').value = syncConfig.token || '';
      $('ghGistIdInput').value = syncConfig.gistId || '';
      switchSyncTab('pair');
    } else if (syncConfig.mode === 'custom') {
      $('customUrlInput').value = syncConfig.url || '';
      $('customAuthHeaderInput').value = syncConfig.authHeader || '';
      switchSyncTab('pair');
    } else {
      switchSyncTab('github');
    }
    refreshPairingOutputs();
    $('syncModal').hidden = false;
  }

  // ============================================================================
  // OLAY DİNLEYİCİLERİ (EVENT LISTENERS)
  // ============================================================================
  function bindEvents() {
    // Navbar.gallery Mega Menu Etkileşimleri
    $('navMegaBoxesBtn').addEventListener('click', (e) => {
      e.stopPropagation();
      const willOpen = $('navMegaBoxesPanel').hidden;
      closeMegaMenus();
      $('navMegaBoxesPanel').hidden = !willOpen;
      $('navMegaBoxesBtn').setAttribute('aria-expanded', String(willOpen));
    });

    $('navMegaCornersBtn').addEventListener('click', (e) => {
      e.stopPropagation();
      const willOpen = $('navMegaCornersPanel').hidden;
      closeMegaMenus();
      $('navMegaCornersPanel').hidden = !willOpen;
      $('navMegaCornersBtn').setAttribute('aria-expanded', String(willOpen));
    });

    document.addEventListener('click', (e) => {
      if (!e.target.closest('.floating-navbar')) {
        closeMegaMenus();
      }
    });

    $('megaMenuNewBoxBtn').addEventListener('click', () => {
      closeMegaMenus();
      openBoxEditModal(null);
    });

    document.querySelectorAll('[data-focus-corner]').forEach((btn) => {
      btn.addEventListener('click', () => focusCornerPanel(btn.dataset.focusCorner));
    });

    // Supahero, CTA.gallery ve Footer.design Aksiyonları
    $('btnHeroSync').addEventListener('click', () => openSyncModal());
    $('btnCtaPair').addEventListener('click', () => openSyncModal('pair'));
    $('btnCtaInstall').addEventListener('click', () => $('btnInstallPwa').click());
    $('btnCtaExport').addEventListener('click', () => $('btnExportJson').click());
    $('footerInstallBtn').addEventListener('click', () => $('btnInstallPwa').click());
    $('footerNewBoxBtn').addEventListener('click', () => openBoxEditModal(null));
    $('btnScrollTop').addEventListener('click', () => window.scrollTo({ top: 0, behavior: 'smooth' }));

    document.querySelectorAll('[data-footer-sync]').forEach((btn) => {
      btn.addEventListener('click', () => openSyncModal(btn.dataset.footerSync));
    });

    document.querySelectorAll('[data-footer-layout]').forEach((btn) => {
      btn.addEventListener('click', () => {
        appState.layoutMode = btn.dataset.footerLayout;
        if (!activeBoxId || $('depoView').hidden) {
          if (appState.boxes.length) openDepoView(appState.boxes[0].id);
        } else {
          applyLayoutModeUI();
        }
        saveStateAndSync();
      });
    });

    // Üst bar navigasyon
    $('btnLogoHome').addEventListener('click', closeDepoView);
    $('btnBackHome').addEventListener('click', closeDepoView);

    $('boxSearchInput').addEventListener('input', renderHomeGrid);
    $('btnAddBox').addEventListener('click', () => openBoxEditModal(null));
    $('btnRenameActiveBox').addEventListener('click', () => {
      if (activeBoxId) openBoxEditModal(activeBoxId);
    });

    // Kutucuk Ekle / Düzenle Modalı
    $('btnCloseBoxEdit').addEventListener('click', closeBoxEditModal);
    $('btnCancelBoxEdit').addEventListener('click', closeBoxEditModal);
    $('boxEditForm').addEventListener('submit', (e) => {
      e.preventDefault();
      const name = $('boxNameInput').value.trim();
      const color = $('boxColorPicker').value || BOX_COLORS[0];
      if (!name) return;

      if (editingBoxId) {
        const box = appState.boxes.find((b) => b.id === editingBoxId);
        if (box) {
          box.name = name;
          box.color = color;
          box.updatedAt = Date.now();
        }
        showToast('Kutucuk güncellendi.', 'success');
      } else {
        const newBox = createBox(name, color, appState.boxes.length + 1);
        appState.boxes.push(newBox);
        showToast(`"${name}" kutucuğu eklendi.`, 'success');
      }

      closeBoxEditModal();
      renderAll();
      saveStateAndSync();
    });

    // Yerleşim Modu (4 Köşe vs Serbest Köşe Masası)
    document.querySelectorAll('#layoutModeToggle .seg-btn').forEach((btn) => {
      btn.addEventListener('click', () => {
        appState.layoutMode = btn.dataset.layout;
        applyLayoutModeUI();
        saveStateAndSync();
      });
    });

    $('btnSnapCorners').addEventListener('click', () => {
      const box = getActiveBox();
      if (!box) return;
      box.hasCustomCornerPos = false;
      snapCornersSymmetrically(box);
      applyFreePositionsToDom(box);
      saveStateAndSync();
      showToast('Paneller 4 köşeye simetrik yerleştirildi.', 'success');
    });

    // Köşe Büyüt / Küçült
    document.querySelectorAll('.btn-expand-corner').forEach((btn) => {
      btn.addEventListener('click', () => {
        const panel = btn.closest('.corner-panel');
        const wasExpanded = panel.classList.contains('expanded');
        collapseAllCorners();
        if (!wasExpanded) {
          panel.classList.add('expanded');
          btn.textContent = '⤡';
        }
      });
    });

    // Köşelerdeki Açılır Ekleme Formları (+ Link Ekle, + Paragraf Yaz, + URL Ekle)
    document.querySelectorAll('[data-toggle-form]').forEach((btn) => {
      btn.addEventListener('click', () => {
        const form = $(btn.dataset.toggleForm);
        if (!form) return;
        form.hidden = !form.hidden;
        if (!form.hidden) {
          const firstInput = form.querySelector('input, textarea');
          if (firstInput) firstInput.focus();
        }
      });
    });

    // Mobil Köşe Sekmeleri
    document.querySelectorAll('#mobileCornerTabs .mob-tab').forEach((tabBtn) => {
      tabBtn.addEventListener('click', () => {
        activeMobileCorner = tabBtn.dataset.tab;
        document.querySelectorAll('#mobileCornerTabs .mob-tab').forEach((b) => b.classList.remove('active'));
        tabBtn.classList.add('active');
        document.querySelectorAll('.corner-panel').forEach((p) => {
          p.classList.toggle(
            'mobile-hidden',
            activeMobileCorner !== 'all' && p.dataset.corner !== activeMobileCorner
          );
        });
      });
    });

    // SOL ÜST KÖŞE: Hızlı Serbest Not Defteri + Maddeli Not
    let scratchpadTimer = null;
    $('quickScratchpad').addEventListener('input', () => {
      const box = getActiveBox();
      if (!box) return;
      box.scratchpad = $('quickScratchpad').value;
      box.updatedAt = Date.now();
      $('scratchpadSavedIndicator').textContent = 'Yazılıyor...';
      clearTimeout(scratchpadTimer);
      scratchpadTimer = setTimeout(() => {
        $('scratchpadSavedIndicator').textContent = 'Kaydedildi ✓';
        saveStateAndSync();
      }, 450);
    });

    $('noteForm').addEventListener('submit', (e) => {
      e.preventDefault();
      const box = getActiveBox();
      const text = $('noteInput').value.trim();
      if (!box || !text) return;
      box.notes.unshift({ id: uid('note'), text, createdAt: Date.now() });
      box.updatedAt = Date.now();
      $('noteInput').value = '';
      renderNotesList(box);
      saveStateAndSync();
    });

    // SAĞ ÜST KÖŞE: Link Ekleme
    $('linkForm').addEventListener('submit', (e) => {
      e.preventDefault();
      const box = getActiveBox();
      const title = $('linkTitleInput').value.trim();
      const url = normalizeUrl($('linkUrlInput').value);
      const desc = $('linkDescInput').value.trim();
      if (!box || !url) return;

      box.links.unshift({
        id: uid('lnk'),
        title: title || extractDomain(url),
        url,
        desc,
        createdAt: Date.now()
      });
      box.updatedAt = Date.now();
      $('linkTitleInput').value = '';
      $('linkUrlInput').value = '';
      $('linkDescInput').value = '';
      $('linkForm').hidden = true;
      renderLinksList(box);
      saveStateAndSync();
    });

    // SOL ALT KÖŞE: Paragraf Ekleme
    $('paragraphForm').addEventListener('submit', (e) => {
      e.preventDefault();
      const box = getActiveBox();
      const title = $('paragraphTitleInput').value.trim();
      const content = $('paragraphContentInput').value.trim();
      if (!box || !content) return;

      box.paragraphs.unshift({
        id: uid('para'),
        title: title || 'Paragraf',
        content,
        createdAt: Date.now()
      });
      box.updatedAt = Date.now();
      $('paragraphTitleInput').value = '';
      $('paragraphContentInput').value = '';
      $('paragraphForm').hidden = true;
      renderParagraphsList(box);
      saveStateAndSync();
    });

    // Paragraf Okuma / Düzenleme Modalı
    $('btnCloseParaModal').addEventListener('click', closeParagraphModal);
    $('btnCopyParaModal').addEventListener('click', () => {
      navigator.clipboard?.writeText($('paraModalBodyInput').value);
      showToast('Paragraf metni kopyalandı.', 'success');
    });
    $('btnSaveParaModal').addEventListener('click', () => {
      if (!editingParaContext) return;
      const box = appState.boxes.find((b) => b.id === editingParaContext.boxId);
      const para = box?.paragraphs.find((p) => p.id === editingParaContext.paraId);
      if (para) {
        para.title = $('paraModalTitleInput').value.trim() || 'Paragraf';
        para.content = $('paraModalBodyInput').value;
        box.updatedAt = Date.now();
        renderParagraphsList(box);
        saveStateAndSync();
        showToast('Paragraf güncellendi.', 'success');
      }
      closeParagraphModal();
    });

    // SAĞ ALT KÖŞE: Resimler (Dosya Seç, Sürükle-Bırak, Ctrl+V, URL)
    const dropZone = $('imageDropZone');
    const fileInput = $('imageFileInput');

    $('btnSelectImage').addEventListener('click', () => fileInput.click());
    fileInput.addEventListener('change', () => {
      if (fileInput.files.length) {
        handleImageFiles(fileInput.files);
        fileInput.value = '';
      }
    });

    dropZone.addEventListener('dragover', (e) => {
      e.preventDefault();
      dropZone.classList.add('drag-over');
    });
    dropZone.addEventListener('dragleave', () => dropZone.classList.remove('drag-over'));
    dropZone.addEventListener('drop', (e) => {
      e.preventDefault();
      dropZone.classList.remove('drag-over');
      if (e.dataTransfer?.files?.length) {
        handleImageFiles(e.dataTransfer.files);
      }
    });

    window.addEventListener('paste', (e) => {
      if (!activeBoxId || !$('depoView') || $('depoView').hidden) return;
      const items = e.clipboardData?.items;
      if (!items) return;
      const imgFiles = [];
      for (const item of items) {
        if (item.type.startsWith('image/')) {
          const f = item.getAsFile();
          if (f) imgFiles.push(f);
        }
      }
      if (imgFiles.length) {
        handleImageFiles(imgFiles);
      }
    });

    $('imageUrlForm').addEventListener('submit', (e) => {
      e.preventDefault();
      const box = getActiveBox();
      const url = normalizeUrl($('imageUrlInput').value);
      const title = $('imageTitleInput').value.trim() || 'Web Resmi';
      if (!box || !url) return;

      box.images.unshift({
        id: uid('img'),
        title,
        dataUrl: url,
        createdAt: Date.now()
      });
      box.updatedAt = Date.now();
      $('imageUrlInput').value = '';
      $('imageTitleInput').value = '';
      $('imageUrlForm').hidden = true;
      renderImagesList(box);
      saveStateAndSync();
    });

    // Lightbox
    $('btnCloseLightbox').addEventListener('click', closeLightbox);
    $('lightboxModal').addEventListener('click', (e) => {
      if (e.target === $('lightboxModal')) closeLightbox();
    });

    // Senkronizasyon Modalı & Butonları
    $('btnOpenSyncModal').addEventListener('click', () => openSyncModal());
    $('btnCloseSyncModal').addEventListener('click', () => ($('syncModal').hidden = true));
    $('btnSyncNow').addEventListener('click', () => pullFromCloud(false, true));

    document.querySelectorAll('.sync-tab').forEach((btn) => {
      btn.addEventListener('click', () => switchSyncTab(btn.dataset.syncTab));
    });

    $('btnConnectGithub').addEventListener('click', connectGithubSync);
    $('btnDisconnectSync').addEventListener('click', disconnectSync);
    $('btnConnectCustom').addEventListener('click', connectCustomSync);
    $('btnDisconnectCustom').addEventListener('click', disconnectSync);

    $('btnCopyPairingLink').addEventListener('click', () => {
      navigator.clipboard?.writeText($('pairingLinkOutput').value);
      showToast('Eşleştirme linki kopyalandı! Telefonuna gönderebilirsin.', 'success');
    });
    $('btnCopyPairingCode').addEventListener('click', () => {
      navigator.clipboard?.writeText($('pairingCodeOutput').value);
      showToast('Eşleştirme kodu kopyalandı.', 'success');
    });
    $('pastePairingCodeInput').addEventListener('input', () => {
      const val = $('pastePairingCodeInput').value.trim();
      $('pairingDecryptWrap').hidden = !val.startsWith('ENC1:');
    });
    $('btnApplyPairingCode').addEventListener('click', () => {
      applyPairingCode($('pastePairingCodeInput').value);
    });

    // Üst Düzey Güvenlik & Kasa Kilidi Modalı
    $('btnOpenSecurityModal').addEventListener('click', openSecurityModal);
    $('footerSecurityBtn').addEventListener('click', openSecurityModal);
    $('btnCloseSecurityModal').addEventListener('click', () => ($('securityModal').hidden = true));
    $('btnLockVaultNow').addEventListener('click', () => lockVaultNow('Kasa manuel olarak kilitlendi.'));

    $('securitySetupForm').addEventListener('submit', async (e) => {
      e.preventDefault();
      const currentPass = $('vaultCurrentPassInput').value;
      const newPass = $('vaultNewPassInput').value;
      const confirmPass = $('vaultConfirmPassInput').value;
      const autoLockMinutes = Number($('autoLockMinutesSelect').value);

      if ((securityMeta.enabled || sessionMasterPassword) && currentPass !== sessionMasterPassword) {
        showToast('Mevcut kasa şifresi hatalı!', 'error');
        return;
      }
      if (newPass.length < 6) {
        showToast('Kasa şifresi en az 6 karakter olmalıdır.', 'warn');
        return;
      }
      if (newPass !== confirmPass) {
        showToast('Yeni şifre ve tekrarı eşleşmiyor.', 'warn');
        return;
      }

      sessionMasterPassword = newPass;
      saveSecurityMeta({ enabled: true, autoLockMinutes });
      await persistLocalState(false);
      await saveSyncConfig(syncConfig);
      if (isCloudConfigured()) {
        await pushToCloud(false);
      }
      resetAutoLockTimer();
      $('securityModal').hidden = true;
      showToast('AES-256-GCM Uçtan Uca Şifreleme aktif edildi!', 'success', 4000);
    });

    $('btnDisableVaultLock').addEventListener('click', async () => {
      const currentPass = $('vaultCurrentPassInput').value;
      if (sessionMasterPassword && currentPass !== sessionMasterPassword) {
        showToast('Şifrelemeyi kaldırmak için mevcut kasa şifrenizi girin.', 'error');
        $('vaultCurrentPassInput').focus();
        return;
      }
      if (!window.confirm('Uçtan uca şifrelemeyi kaldırmak istediğinize emin misiniz? Veriler yerel cihazda ve bulutta şifresiz saklanacaktır.')) {
        return;
      }
      sessionMasterPassword = null;
      clearTimeout(autoLockTimer);
      saveSecurityMeta({ enabled: false, autoLockMinutes: 5 });
      await persistLocalState(false);
      await saveSyncConfig(syncConfig);
      if (isCloudConfigured()) {
        await pushToCloud(false);
      }
      $('securityModal').hidden = true;
      showToast('Kasa şifresi kaldırıldı.', 'info');
    });

    // Kasa Kilit Ekranı (Unlock & Brute-Force Koruması)
    $('vaultUnlockForm').addEventListener('submit', async (e) => {
      e.preventDefault();
      const errEl = $('vaultUnlockError');
      const now = Date.now();
      if (now < lockoutUntil) {
        const secs = Math.ceil((lockoutUntil - now) / 1000);
        errEl.textContent = `Çok fazla hatalı deneme! ${secs} saniye bekleyin.`;
        errEl.hidden = false;
        return;
      }

      const pass = $('vaultUnlockPassInput').value;
      if (!pass) return;

      try {
        if (pendingRemoteEnvelope) {
          const decryptedRemote = await VaultCrypto.decryptPayload(pendingRemoteEnvelope, pass);
          sessionMasterPassword = pass;
          appState = sanitizeState(decryptedRemote);
          pendingRemoteEnvelope = null;
          isVaultLocked = false;
          saveSecurityMeta({ enabled: true, autoLockMinutes: securityMeta.autoLockMinutes });
          await persistLocalState(false);
          await saveSyncConfig(syncConfig);
        } else {
          if (lockedLocalEnvelope && VaultCrypto.isEncryptedEnvelope(lockedLocalEnvelope)) {
            const decryptedState = await VaultCrypto.decryptPayload(lockedLocalEnvelope, pass);
            appState = sanitizeState(decryptedState);
          } else {
            appState = lockedLocalEnvelope ? sanitizeState(lockedLocalEnvelope) : createInitialState();
          }

          if (lockedSyncEnvelope && VaultCrypto.isEncryptedEnvelope(lockedSyncEnvelope)) {
            syncConfig = await VaultCrypto.decryptPayload(lockedSyncEnvelope, pass);
            lockedSyncEnvelope = null;
          } else {
            syncConfig = loadSyncConfigRaw();
          }

          sessionMasterPassword = pass;
          lockedLocalEnvelope = null;
          isVaultLocked = false;
        }

        failedUnlockAttempts = 0;
        lockoutUntil = 0;
        errEl.hidden = true;
        $('vaultUnlockPassInput').value = '';
        $('vaultLockOverlay').hidden = true;

        updateSecurityUI();
        renderAll();
        resetAutoLockTimer();
        await checkUrlPairingParam();
        if (isCloudConfigured()) {
          pullFromCloud(false, false);
        }
        showToast('Kasa kilidi açıldı.', 'success');
      } catch {
        failedUnlockAttempts += 1;
        if (failedUnlockAttempts >= 5) {
          lockoutUntil = Date.now() + 30000;
          errEl.textContent = '5 hatalı deneme! Güvenlik nedeniyle 30 saniye kilitlendi.';
        } else {
          errEl.textContent = `Hatalı kasa şifresi! (Kalan deneme: ${5 - failedUnlockAttempts})`;
        }
        errEl.hidden = false;
        $('vaultUnlockPassInput').select();
      }
    });

    $('btnVaultEmergencyReset').addEventListener('click', async () => {
      if (!window.confirm('DİKKAT: Şifrenizi unuttuysanız bu cihazdaki şifreli yerel veriler silinecektir. Devam etmek istiyor musunuz?')) {
        return;
      }
      if (!window.confirm('Son onay: Bu cihazdaki tüm yerel depolar ve eşleştirme bilgileri sıfırlansın mı?')) {
        return;
      }
      localStorage.removeItem(LS_BACKUP_KEY);
      localStorage.removeItem(LS_SYNC_CONFIG_KEY);
      localStorage.removeItem(LS_SECURITY_META_KEY);
      try {
        await idbSet(STATE_KEY, null);
      } catch {
        // ignore
      }
      window.location.reload();
    });

    // Hareketsizlik sayacını sıfırla
    ['pointerdown', 'keydown', 'touchstart'].forEach((evt) => {
      window.addEventListener(evt, () => {
        if (sessionMasterPassword && !isVaultLocked) {
          resetAutoLockTimer();
        }
      }, { passive: true });
    });

    // JSON Yedekleme
    $('btnExportJson').addEventListener('click', () => {
      if (isVaultLocked) return;
      const blob = new Blob([JSON.stringify(appState, null, 2)], { type: 'application/json' });
      const url = URL.createObjectURL(blob);
      const a = document.createElement('a');
      a.href = url;
      a.download = `depokutusu-yedek-${new Date().toISOString().slice(0, 10)}.json`;
      a.click();
      URL.revokeObjectURL(url);
      showToast('JSON yedeği indirildi.', 'success');
    });

    $('importJsonInput').addEventListener('change', (e) => {
      const file = e.target.files?.[0];
      if (!file) return;
      const reader = new FileReader();
      reader.onload = async () => {
        try {
          const imported = sanitizeState(JSON.parse(reader.result));
          imported.isPristineDefault = false;
          imported.updatedAt = Date.now();
          appState = imported;
          await persistLocalState(false);
          renderAll();
          scheduleCloudPush();
          $('syncModal').hidden = true;
          showToast('Yedek başarıyla geri yüklendi!', 'success');
        } catch {
          showToast('Geçersiz JSON yedek dosyası.', 'error');
        }
      };
      reader.readAsText(file);
      e.target.value = '';
    });

    // PWA Kurulumu
    window.addEventListener('beforeinstallprompt', (e) => {
      e.preventDefault();
      deferredInstallPrompt = e;
    });

    $('btnInstallPwa').addEventListener('click', async () => {
      if (deferredInstallPrompt) {
        deferredInstallPrompt.prompt();
        const choice = await deferredInstallPrompt.userChoice;
        if (choice.outcome === 'accepted') {
          showToast('DepoKutusu cihazınıza kuruluyor!', 'success');
        }
        deferredInstallPrompt = null;
      } else {
        $('iosInstallModal').hidden = false;
      }
    });
    $('btnCloseIosModal').addEventListener('click', () => ($('iosInstallModal').hidden = true));
    $('btnOkIosModal').addEventListener('click', () => ($('iosInstallModal').hidden = true));

    // ESC ile açık modalları kapat
    window.addEventListener('keydown', (e) => {
      if (e.key === 'Escape') {
        closeLightbox();
        closeBoxEditModal();
        closeParagraphModal();
        $('syncModal').hidden = true;
        $('securityModal').hidden = true;
        $('iosInstallModal').hidden = true;
        closeMegaMenus();
        collapseAllCorners();
      }
    });

    // Sekme gizlendiğinde anında kilitleme veya görünür olunca bulut kontrolü
    document.addEventListener('visibilitychange', () => {
      if (document.visibilityState === 'hidden') {
        if (sessionMasterPassword && Number(securityMeta.autoLockMinutes) === -1) {
          lockVaultNow('Sekme değiştirildiği için kasa güvenlik amacıyla kilitlendi.');
        }
        return;
      }
      if (document.visibilityState === 'visible' && !isVaultLocked && isCloudConfigured()) {
        pullFromCloud(false, false);
      }
    });

    // Ekran yeniden boyutlandırmada serbest köşe masası sınırlarını koru
    window.addEventListener('resize', () => {
      const box = getActiveBox();
      if (box && appState.layoutMode === 'free' && window.innerWidth >= 900) {
        resolveCollisions('notes', box.cornerPositions, getContainerBounds());
        applyFreePositionsToDom(box);
      } else if (box) {
        applyFreePositionsToDom(box);
      }
    });
  }

  // ============================================================================
  // BAŞLATMA (BOOT)
  // ============================================================================
  async function init() {
    const rawLocal = await loadLocalStateRaw();
    const needsUnlock =
      VaultCrypto.isEncryptedEnvelope(rawLocal) ||
      Boolean(lockedSyncEnvelope) ||
      securityMeta.enabled;

    if (needsUnlock) {
      lockedLocalEnvelope = rawLocal;
      appState = createInitialState();
    } else {
      appState = rawLocal ? sanitizeState(rawLocal) : createInitialState();
    }

    bindEvents();
    setupFreeCanvasDragAndResize();
    updateSecurityUI();

    // Service Worker kaydı (GitHub Pages + PWA desteği)
    if ('serviceWorker' in navigator) {
      navigator.serviceWorker
        .register('./sw.js', { updateViaCache: 'none' })
        .then((reg) => reg.update().catch(() => {}))
        .catch((err) => {
          console.warn('Service Worker kaydı atlandı:', err);
        });
    }

    if (needsUnlock) {
      showVaultLockOverlay();
    } else {
      renderAll();
      await checkUrlPairingParam();
      if (!isVaultLocked && isCloudConfigured()) {
        pullFromCloud(false, false);
      }
    }

    // 30 saniyede bir arka plan senkron kontrolü (kasa açıkken)
    cloudPullInterval = setInterval(() => {
      if (
        document.visibilityState === 'visible' &&
        !isVaultLocked &&
        isCloudConfigured() &&
        !cloudPushTimer
      ) {
        pullFromCloud(false, false);
      }
    }, 30000);
  }

  init();
})();
