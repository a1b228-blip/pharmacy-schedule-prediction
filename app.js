'use strict';

/* ============================================================================
 * 佳里奇美醫院藥劑科小夜輪值順序預測系統（修正版：三軌並行與同日互斥）
 * app.js — 三軌平行交棒排班引擎、同日互斥防呆、預假即時重算與 DOM 渲染
 *
 * 本檔為純前端原生 JavaScript，無任何外部套件依賴，直接以瀏覽器開啟
 * index.html 即可離線運作。
 * ==========================================================================*/

/* ----------------------------------------------------------------------------
 * 一、基礎資料設定
 * --------------------------------------------------------------------------*/

// 小夜輪值池：13 位藥師，依循環輪替之預設順序排列（陣列索引 0 起算）
const ROTATION_POOL = [
  '馨霈', '博茹', '曼如', '斐庭', '佳霙', '婌伶', '國棟',
  '芸妮', '薏華', '銘豐', '玲嬋', '景毅', '嘉怡'
];

// 全科同仁名冊（含不參與小夜輪值者，僅供顯示與預假表單防呆使用）
const ALL_STAFF = ROTATION_POOL.concat(['淑鈴']);

// 淑鈴：夜班資格為「否」，100% 不進入小夜輪值池，系統標記為僅排日班
const NIGHT_SHIFT_EXCLUDED = ['淑鈴'];

// 小夜輪值班別代碼與顯示名稱
const SHIFT_TYPES = ['E', 'L3', 'L2'];
const SHIFT_LABELS = { E: 'E 班', L3: 'L3 班', L2: 'L2 班' };

// 排班預測模擬範圍：涵蓋 10 / 11 / 12 月，確保跨月的 5 天週期可連續推演
const SIM_START_DATE = '2026-10-01';
const SIM_END_DATE = '2026-12-31';

// 可切換檢視之月份
const VIEW_MONTHS = [
  { key: '2026-10', label: '115年10月' },
  { key: '2026-11', label: '115年11月' },
  { key: '2026-12', label: '115年12月' }
];

const WEEKDAY_LABELS = ['日', '一', '二', '三', '四', '五', '六'];

// Q4 已知預排假資料（民國 115 年 = 西元 2026 年），供主管直接測試演算法
const DEFAULT_LEAVE_RECORDS = [
  { id: 'seed-1', name: '芸妮', start: '2026-10-02', end: '2026-10-14', note: 'Q4 預排假' },
  { id: 'seed-2', name: '馨霈', start: '2026-10-21', end: '2026-10-30', note: 'Q4 預排假' },
  { id: 'seed-3', name: '曼如', start: '2026-10-31', end: '2026-11-08', note: 'Q4 預排假' },
  { id: 'seed-4', name: '博茹', start: '2026-11-09', end: '2026-11-21', note: 'Q4 預排假' },
  { id: 'seed-5', name: '國棟', start: '2026-11-26', end: '2026-12-08', note: 'Q4 預排假' }
];

// localStorage 存檔鍵值（僅存於本機瀏覽器，離線亦可保留主管操作紀錄）
const STORAGE_KEY_LEAVES = 'pharm_night_rotation_v2__leaves';
const STORAGE_KEY_OFFSETS = 'pharm_night_rotation_v2__offsets';

/* ----------------------------------------------------------------------------
 * 二、可變狀態
 * --------------------------------------------------------------------------*/

let leaveRecords = [];

// 三軌各自的「起跑順位」（輪值池索引）。依規格書：
// 第 1 天（10/01）E 軌由順位 1（馨霈）領跑、L3 軌由順位 2（博茹）領跑、
// L2 軌由順位 3（曼如）領跑，確保起跑當下三人互不相同。
let shiftStartIndex = { E: 0, L3: 1, L2: 2 };

let state = {
  currentMonth: '2026-10',   // 目前檢視月份
  currentShift: 'ALL'        // 目前檢視班別：'ALL' | 'E' | 'L3' | 'L2'
};

// 排班模擬結果快取：{ E: {dailyMap, turns, skippedTurns}, L3: {...}, L2: {...} }
let scheduleData = {};

// 全域防呆檢核結果（每日三班互斥／淑鈴排除／無人連續超過 5 天）
let validationResults = {};

/* ----------------------------------------------------------------------------
 * 三、日期工具函式
 * --------------------------------------------------------------------------*/

function pad2(n) { return String(n).padStart(2, '0'); }

// Date 物件 -> 'YYYY-MM-DD' 字串
function fmtDate(d) {
  return `${d.getFullYear()}-${pad2(d.getMonth() + 1)}-${pad2(d.getDate())}`;
}

// 'YYYY-MM-DD' 字串 -> Date 物件（採本地時間，避免時區位移造成日期誤差）
function parseDate(s) {
  const [y, m, d] = s.split('-').map(Number);
  return new Date(y, m - 1, d);
}

function addDays(d, n) {
  const nd = new Date(d);
  nd.setDate(nd.getDate() + n);
  return nd;
}

// 判斷某人於某日是否處於預假狀態
function isOnLeave(name, dateStr) {
  return leaveRecords.some(r => r.name === name && dateStr >= r.start && dateStr <= r.end);
}

/* ----------------------------------------------------------------------------
 * 四、核心演算法：三軌並行交棒 ＋ 同日同人絕對互斥 ＋ 防過勞
 *
 * 規則摘要：
 *   1. E / L3 / L2 三個小夜班別「每天」都各需 1 人，且當天 3 位人員必須完全不同
 *      （同日互斥剛性防呆）；同一人也不可在未休息的情況下緊接著跨軌上班（防過勞）。
 *   2. 三軌各自以「連續 5 天」為一個基本值勤區塊，區塊期滿或值勤中途遇到預假／
 *      衝突時即結束，並立即依輪值池順位向下尋找下一個「合格接棒者」。
 *   3. 合格接棒者需同時滿足：
 *        a) 無衝突：接棒期間內未同時在其他軌值勤（同日互斥的延伸判斷）。
 *        b) 無預假：接棒期間內沒有登記預假。
 *        c) 防過勞：不會造成本人連續值勤超過 5 天（緊接前一天已值勤者不得再接）。
 *      若順位人員當下不合格，暫時跳過往下一順位尋找，其輪值權益保留至輪值池
 *      下一輪自然轉回時再行考慮（不從池中除名，只是延後）。
 * --------------------------------------------------------------------------*/

function simulateAllTracks() {
  const pool = ROTATION_POOL;
  const simStart = parseDate(SIM_START_DATE);
  const simEnd = parseDate(SIM_END_DATE);

  const dailyMap = { E: {}, L3: {}, L2: {} };
  const turns = { E: [], L3: [], L2: [] };
  const skippedCandidates = { E: [], L3: [], L2: [] };

  // 每人已委派值勤日期集合（不分班別，用於互斥與防過勞判斷）
  const personWorkSet = {};
  ROTATION_POOL.forEach(n => { personWorkSet[n] = new Set(); });

  function workedOn(name, dateStr) {
    return personWorkSet[name].has(dateStr);
  }

  function isBusyAnyTrack(name, dateStr) {
    return SHIFT_TYPES.some(st => dailyMap[st][dateStr] && dailyMap[st][dateStr].person === name);
  }

  // 評估某候選人自 startDate 起最多可連續值勤幾天（上限 5 天，或至模擬範圍結束）
  function evalCandidate(name, startDate) {
    const yesterday = fmtDate(addDays(startDate, -1));
    if (workedOn(name, yesterday)) {
      return { length: 0, stopReason: 'fatigue' }; // 前一天才剛值勤，防過勞不得緊接著再上
    }
    let len = 0;
    let stopReason = null;
    for (let i = 0; i < 5; i++) {
      const d = addDays(startDate, i);
      if (d.getTime() > simEnd.getTime()) break;
      const dStr = fmtDate(d);
      if (isOnLeave(name, dStr)) { stopReason = 'leave'; break; }
      if (isBusyAnyTrack(name, dStr)) { stopReason = 'conflict'; break; }
      len++;
    }
    return { length: len, stopReason };
  }

  function skipReasonLabel(reason) {
    if (reason === 'leave') return '該時段已登記預假';
    if (reason === 'conflict') return '同時段已在其他班別值勤（互斥防呆）';
    if (reason === 'fatigue') return '前一日已值勤，防過勞需先休息';
    return '無法排入';
  }

  // 依輪值池順位（自 fromIndex 起）尋找合格接棒者：
  // 優先選出可「完整值滿 5 天」（或值到模擬範圍結尾）之第一位合格者；
  // 若全池皆無法完整值滿，退而求其次選可值勤天數最多者，確保當天仍有人可派。
  function findCandidate(track, fromIndex, startDate) {
    const scanned = [];
    for (let step = 0; step < pool.length; step++) {
      const idx = (fromIndex + step) % pool.length;
      const name = pool[idx];
      const ev = evalCandidate(name, startDate);
      scanned.push({ idx, name, length: ev.length, stopReason: ev.stopReason });

      const reachesSimEnd = ev.length > 0 &&
        fmtDate(addDays(startDate, ev.length - 1)) === fmtDate(simEnd);

      // 符合規格書核心：「某員工值班中途遇預假（如值到第3天請假），該員值完前段天數，
      // 並於預假當日立即由下一個順位接手排滿 5 天」
      const canStartAndHandoffOnLeave = ev.length > 0 && ev.stopReason === 'leave';

      if (ev.length >= 5 || reachesSimEnd || canStartAndHandoffOnLeave) {
        scanned.slice(0, -1).forEach(s => {
          skippedCandidates[track].push({
            shiftType: track, person: s.name, date: fmtDate(startDate),
            reason: skipReasonLabel(s.stopReason)
          });
        });
        return { idx, name, length: ev.length, stopReason: ev.stopReason };
      }
    }

    // 全池都無法完整值滿：選可值勤天數最多者（同天數則取順位在前者）
    let best = scanned[0];
    scanned.forEach(s => { if (s.length > best.length) best = s; });
    scanned.forEach(s => {
      if (s !== best) {
        skippedCandidates[track].push({
          shiftType: track, person: s.name, date: fmtDate(startDate),
          reason: skipReasonLabel(s.stopReason)
        });
      }
    });
    if (best.length === 0) return null; // 理論極端情況：全員皆無法值勤
    return { idx: best.idx, name: best.name, length: best.length, stopReason: best.stopReason };
  }

  // 三軌搜尋起點（下一次需要決策時，從此輪值池索引開始往下找）
  const trackPointer = { E: shiftStartIndex.E, L3: shiftStartIndex.L3, L2: shiftStartIndex.L2 };
  // 三軌目前已委派區塊的結束日期（Date 物件）；null 代表尚未指派、需立即決策
  const trackBlockEnd = { E: null, L3: null, L2: null };
  const trackTurnNo = { E: 0, L3: 0, L2: 0 };

  let cursor = new Date(simStart);
  while (cursor.getTime() <= simEnd.getTime()) {
    // 依 E → L3 → L2 優先順序決策，確保同一天內後決策的班別能看到前面班別
    // 剛剛委派出去的人員，藉此天生滿足「同日互斥」與跨軌防過勞判斷。
    SHIFT_TYPES.forEach(track => {
      const needsNewBlock = trackBlockEnd[track] === null || cursor.getTime() > trackBlockEnd[track].getTime();
      if (!needsNewBlock) return;

      const turnStartStr = fmtDate(cursor);
      const result = findCandidate(track, trackPointer[track], cursor);

      if (!result || result.length === 0) {
        // 全員皆無法值勤（理論極端情況）：本日該軌從缺，隔天重新嘗試
        dailyMap[track][turnStartStr] = { shiftType: track, person: null, unassigned: true };
        trackBlockEnd[track] = new Date(cursor);
        return;
      }

      trackTurnNo[track]++;
      const endDate = addDays(cursor, result.length - 1);

      for (let i = 0; i < result.length; i++) {
        const d = addDays(cursor, i);
        const dStr = fmtDate(d);
        dailyMap[track][dStr] = {
          shiftType: track, person: result.name,
          dayInTurn: i + 1, turnNo: trackTurnNo[track]
        };
        personWorkSet[result.name].add(dStr);
      }

      const reason = result.length >= 5 ? 'full5'
        : (fmtDate(endDate) === fmtDate(simEnd) ? 'inProgress' : 'earlyEnd');

      turns[track].push({
        no: trackTurnNo[track], shiftType: track, person: result.name,
        startDate: turnStartStr, endDate: fmtDate(endDate), days: result.length,
        reason, stopReason: result.stopReason
      });

      trackPointer[track] = (result.idx + 1) % pool.length;
      trackBlockEnd[track] = endDate;
    });

    cursor = addDays(cursor, 1);
  }

  // 後製處理：標記「提早結束 ➔ 下一棒接手」的交棒關聯，供月曆與時間軸標註 🔁
  SHIFT_TYPES.forEach(track => {
    const list = turns[track];
    for (let i = 1; i < list.length; i++) {
      if (list[i - 1].reason === 'earlyEnd') {
        list[i].cameFromHandoff = true;
        list[i].handoffFromPerson = list[i - 1].person;
        list[i - 1].handoffToPerson = list[i].person;
        if (dailyMap[track][list[i].startDate]) {
          dailyMap[track][list[i].startDate].isHandoffDay = true;
          dailyMap[track][list[i].startDate].handoffFromPerson = list[i - 1].person;
        }
        if (dailyMap[track][list[i - 1].endDate]) {
          dailyMap[track][list[i - 1].endDate].handoffTo = list[i].person;
        }
      }
    }
  });

  return { dailyMap, turns, skippedCandidates };
}

function stopReasonText(reason) {
  if (reason === 'leave') return '遇預假';
  if (reason === 'conflict') return '同時段其他班別衝突';
  if (reason === 'fatigue') return '防過勞需先休息';
  return '';
}

/* ----------------------------------------------------------------------------
 * 五、全域防呆檢核（每日三班互斥／淑鈴排除／無人連續超過 5 天）
 * --------------------------------------------------------------------------*/

function computeValidationResults(dailyMap) {
  const results = {
    mutualExclusion: { pass: true, violations: [] },
    shuLingExcluded: { pass: true, violations: [] },
    maxConsecutive: { pass: true, violations: [] }
  };

  const simStart = parseDate(SIM_START_DATE);
  const simEnd = parseDate(SIM_END_DATE);

  // 檢核一 + 二：逐日檢查三班互斥、以及是否誤排淑鈴
  let d = new Date(simStart);
  while (d.getTime() <= simEnd.getTime()) {
    const dStr = fmtDate(d);
    const names = SHIFT_TYPES.map(st => dailyMap[st][dStr] && dailyMap[st][dStr].person).filter(Boolean);

    if (new Set(names).size !== names.length) {
      results.mutualExclusion.pass = false;
      results.mutualExclusion.violations.push(dStr);
    }
    if (names.includes('淑鈴')) {
      results.shuLingExcluded.pass = false;
      results.shuLingExcluded.violations.push(dStr);
    }
    d = addDays(d, 1);
  }

  // 檢核三：無人連續超過 5 天（跨班別、以人為單位計算實際值勤日）
  const personDates = {};
  ROTATION_POOL.forEach(n => { personDates[n] = new Set(); });
  d = new Date(simStart);
  while (d.getTime() <= simEnd.getTime()) {
    const dStr = fmtDate(d);
    SHIFT_TYPES.forEach(st => {
      const p = dailyMap[st][dStr] && dailyMap[st][dStr].person;
      if (p) personDates[p].add(dStr);
    });
    d = addDays(d, 1);
  }
  ROTATION_POOL.forEach(name => {
    const dates = [...personDates[name]].sort();
    let run = 0, prevDate = null;
    dates.forEach(ds => {
      if (prevDate && fmtDate(addDays(parseDate(prevDate), 1)) === ds) run++; else run = 1;
      if (run > 5) {
        results.maxConsecutive.pass = false;
        results.maxConsecutive.violations.push(`${name} 於 ${ds} 已連續第 ${run} 天`);
      }
      prevDate = ds;
    });
  });

  return results;
}

// 重新計算三條班別軌道之完整排班預測（任何預假異動或起始設定變更後呼叫）
function recomputeSchedule() {
  const { dailyMap, turns, skippedCandidates } = simulateAllTracks();
  scheduleData = {};
  SHIFT_TYPES.forEach(st => {
    scheduleData[st] = { dailyMap: dailyMap[st], turns: turns[st], skippedTurns: skippedCandidates[st] };
  });
  validationResults = computeValidationResults(dailyMap);
}

/* ----------------------------------------------------------------------------
 * 六、本機儲存（localStorage）
 * --------------------------------------------------------------------------*/

function saveToStorage() {
  try {
    localStorage.setItem(STORAGE_KEY_LEAVES, JSON.stringify(leaveRecords));
    localStorage.setItem(STORAGE_KEY_OFFSETS, JSON.stringify(shiftStartIndex));
  } catch (e) {
    // 私密瀏覽模式或儲存空間受限時，靜默略過，不影響本次操作畫面
  }
}

function loadFromStorage() {
  try {
    const savedLeaves = localStorage.getItem(STORAGE_KEY_LEAVES);
    const savedOffsets = localStorage.getItem(STORAGE_KEY_OFFSETS);
    leaveRecords = savedLeaves ? JSON.parse(savedLeaves) : DEFAULT_LEAVE_RECORDS.map(r => ({ ...r }));
    if (savedOffsets) shiftStartIndex = Object.assign({ E: 0, L3: 1, L2: 2 }, JSON.parse(savedOffsets));
  } catch (e) {
    leaveRecords = DEFAULT_LEAVE_RECORDS.map(r => ({ ...r }));
  }
}

function resetToDefaults() {
  const ok = window.confirm('確定要重置為系統預設值嗎？\n將清除所有自訂預假登記與起始人員設定，還原為 Q4 預載測試資料。');
  if (!ok) return;
  leaveRecords = DEFAULT_LEAVE_RECORDS.map(r => ({ ...r }));
  shiftStartIndex = { E: 0, L3: 1, L2: 2 };
  saveToStorage();
  recomputeSchedule();
  renderAll();
}

/* ----------------------------------------------------------------------------
 * 七、渲染：防呆檢核綠燈
 * --------------------------------------------------------------------------*/

function renderValidationBar() {
  const bar = document.getElementById('validationBar');
  if (!bar) return;
  const items = [
    { key: 'mutualExclusion', label: '每日 3 班互斥檢驗' },
    { key: 'shuLingExcluded', label: '淑鈴排除確認' },
    { key: 'maxConsecutive', label: '無人連續超過 5 天' }
  ];
  bar.innerHTML = items.map(it => {
    const r = validationResults[it.key];
    const ok = r && r.pass;
    const detail = ok ? '' : escapeHtml((r.violations || []).slice(0, 5).join('；'));
    return `<span class="validation-badge ${ok ? 'validation-badge--pass' : 'validation-badge--fail'}" title="${detail}">${ok ? '✅' : '❌'} ${it.label}${ok ? '通過' : '未通過'}</span>`;
  }).join('');
}

/* ----------------------------------------------------------------------------
 * 八、渲染：頂部工具列（月份 / 班別切換）
 * --------------------------------------------------------------------------*/

function renderToolbar() {
  const monthTabs = document.getElementById('monthTabs');
  monthTabs.innerHTML = VIEW_MONTHS.map(m => `
    <button class="tab ${state.currentMonth === m.key ? 'active' : ''}" data-month="${m.key}">${m.label}</button>
  `).join('');

  const shiftTabs = document.getElementById('shiftTabs');
  const shiftOptions = [{ key: 'ALL', label: '全部' }].concat(SHIFT_TYPES.map(s => ({ key: s, label: SHIFT_LABELS[s] })));
  shiftTabs.innerHTML = shiftOptions.map(s => `
    <button class="tab tab--shift-${s.key} ${state.currentShift === s.key ? 'active' : ''}" data-shift="${s.key}">${s.label}</button>
  `).join('');

  // 進階設定：各班別起跑順位（下拉選單）
  SHIFT_TYPES.forEach(st => {
    const sel = document.getElementById(`offsetSelect-${st}`);
    if (!sel) return;
    sel.innerHTML = ROTATION_POOL.map((name, i) => `<option value="${i}">${i + 1}. ${name}</option>`).join('');
    sel.value = String(shiftStartIndex[st] || 0);
  });
}

/* ----------------------------------------------------------------------------
 * 九、渲染：預假登記面板
 * --------------------------------------------------------------------------*/

function renderLeavePanel() {
  const nameSelect = document.getElementById('leaveNameSelect');
  nameSelect.innerHTML = ROTATION_POOL.map(n => `<option value="${n}">${n}</option>`).join('');

  const list = document.getElementById('leaveList');
  if (leaveRecords.length === 0) {
    list.innerHTML = '<p class="empty-hint">目前尚無預假登記資料。</p>';
    return;
  }

  const sorted = [...leaveRecords].sort((a, b) => a.start.localeCompare(b.start));
  list.innerHTML = sorted.map(r => `
    <div class="leave-item">
      <div class="leave-item__main">
        <span class="leave-item__name">${r.name}</span>
        <span class="leave-item__range">${r.start} ～ ${r.end}</span>
      </div>
      <div class="leave-item__meta">${r.note ? escapeHtml(r.note) : ''}</div>
      <button class="leave-item__del" data-del-id="${r.id}" title="刪除此筆預假">✕</button>
    </div>
  `).join('');
}

function escapeHtml(s) {
  const div = document.createElement('div');
  div.textContent = s;
  return div.innerHTML;
}

/* ----------------------------------------------------------------------------
 * 十、渲染：排班預測月曆
 * --------------------------------------------------------------------------*/

function getMonthMeta(monthKey) {
  const [y, m] = monthKey.split('-').map(Number);
  const daysInMonth = new Date(y, m, 0).getDate();
  const startWeekday = new Date(y, m - 1, 1).getDay(); // 0 = 週日
  return { year: y, month: m, daysInMonth, startWeekday };
}

function activeShiftList() {
  return state.currentShift === 'ALL' ? SHIFT_TYPES : [state.currentShift];
}

function renderCalendar() {
  const grid = document.getElementById('calendarGrid');
  const meta = getMonthMeta(state.currentMonth);
  const shifts = activeShiftList();
  const violationDates = new Set((validationResults.mutualExclusion && validationResults.mutualExclusion.violations) || []);

  let cellsHtml = '';

  // 前導空白格（對齊週日起始）
  for (let i = 0; i < meta.startWeekday; i++) {
    cellsHtml += '<div class="calendar-cell calendar-cell--empty"></div>';
  }

  for (let day = 1; day <= meta.daysInMonth; day++) {
    const dateStr = `${meta.year}-${pad2(meta.month)}-${pad2(day)}`;
    const dateObj = new Date(meta.year, meta.month - 1, day);
    const isWeekend = dateObj.getDay() === 0 || dateObj.getDay() === 6;
    const isViolation = violationDates.has(dateStr);

    let shiftRows = '';
    shifts.forEach(st => {
      const entry = scheduleData[st] && scheduleData[st].dailyMap[dateStr];
      if (!entry || !entry.person) {
        shiftRows += `<div class="cell-shift-row cell-shift-row--empty"><span class="shift-code">${st}</span><span class="shift-person">—</span></div>`;
        return;
      }
      const handoffOutMark = entry.handoffTo ? `<span class="handoff-tag" title="提早結束交棒給 ${entry.handoffTo}">🔁 交棒給 ${entry.handoffTo}</span>` : '';
      const handoffInMark = entry.isHandoffDay ? `<span class="handoff-in-tag" title="自 ${entry.handoffFromPerson} 中途接棒，起算連續值勤">🔁 接棒(原:${entry.handoffFromPerson})</span>` : '';
      shiftRows += `
        <div class="cell-shift-row">
          <span class="shift-badge shift-badge--${st}" title="第 ${entry.turnNo} 棒．第 ${entry.dayInTurn}/5 天">
            <span class="shift-code">${st}</span>${entry.person}
          </span>
          ${handoffOutMark}${handoffInMark}
        </div>`;
    });

    // 當日預假中人員（灰色反灰呈現）
    const onLeaveToday = leaveRecords.filter(r => dateStr >= r.start && dateStr <= r.end);
    const leaveRows = onLeaveToday.map(r => `<span class="leave-tag" title="${escapeHtml(r.note || '')}">🏖️ ${r.name} 預假</span>`).join('');

    cellsHtml += `
      <div class="calendar-cell ${isWeekend ? 'calendar-cell--weekend' : ''} ${isViolation ? 'calendar-cell--violation' : ''}">
        <div class="calendar-cell__date">${day}<span class="calendar-cell__weekday">${WEEKDAY_LABELS[dateObj.getDay()]}</span></div>
        <div class="calendar-cell__shifts">${shiftRows}</div>
        ${leaveRows ? `<div class="calendar-cell__leaves">${leaveRows}</div>` : ''}
      </div>`;
  }

  // 尾端補齊空白格，維持每列 7 格
  const totalCells = meta.startWeekday + meta.daysInMonth;
  const trailing = (7 - (totalCells % 7)) % 7;
  for (let i = 0; i < trailing; i++) {
    cellsHtml += '<div class="calendar-cell calendar-cell--empty"></div>';
  }

  grid.innerHTML = cellsHtml;
}

/* ----------------------------------------------------------------------------
 * 十一、渲染：本月統計
 * --------------------------------------------------------------------------*/

function renderStats() {
  const container = document.getElementById('statsGrid');
  const meta = getMonthMeta(state.currentMonth);
  const shifts = activeShiftList();

  const dayCounts = {};   // 姓名 -> 值班天數
  const turnCounts = {};  // 姓名 -> 棒次數（依 班別-棒次編號 去重）
  ROTATION_POOL.forEach(n => { dayCounts[n] = 0; turnCounts[n] = new Set(); });

  for (let day = 1; day <= meta.daysInMonth; day++) {
    const dateStr = `${meta.year}-${pad2(meta.month)}-${pad2(day)}`;
    shifts.forEach(st => {
      const entry = scheduleData[st] && scheduleData[st].dailyMap[dateStr];
      if (entry && entry.person) {
        dayCounts[entry.person]++;
        turnCounts[entry.person].add(`${st}-${entry.turnNo}`);
      }
    });
  }

  const rows = ROTATION_POOL
    .map(n => ({ name: n, days: dayCounts[n], turns: turnCounts[n].size }))
    .filter(r => r.days > 0)
    .sort((a, b) => b.days - a.days);

  const maxDays = Math.max(1, ...rows.map(r => r.days));

  if (rows.length === 0) {
    container.innerHTML = '<p class="empty-hint">本月尚無排班資料。</p>';
    return;
  }

  container.innerHTML = rows.map(r => `
    <div class="stats-row">
      <span class="stats-row__name">${r.name}</span>
      <div class="stats-row__bar-track">
        <div class="stats-row__bar-fill" style="width:${(r.days / maxDays) * 100}%"></div>
      </div>
      <span class="stats-row__value">${r.days} 天 / ${r.turns} 棒次</span>
    </div>
  `).join('');
}

/* ----------------------------------------------------------------------------
 * 十二、渲染：輪值序列推演表（Sequence Timeline）
 * --------------------------------------------------------------------------*/

function renderTimeline() {
  const container = document.getElementById('timelineTracks');
  const shifts = activeShiftList();

  container.innerHTML = shifts.map(st => {
    const data = scheduleData[st];
    if (!data) return '';

    const cardsHtml = data.turns.map(t => {
      const reasonClass = t.reason === 'earlyEnd' ? 'timeline-card--handoff'
        : t.reason === 'inProgress' ? 'timeline-card--inprogress' : 'timeline-card--full5';

      let statusLine = '';
      if (t.reason === 'full5') {
        statusLine = `值滿 ${t.days} 天`;
      } else if (t.reason === 'earlyEnd') {
        const why = stopReasonText(t.stopReason);
        statusLine = t.handoffToPerson
          ? `值 ${t.days} 天（${why}）提早交棒 ➔ 接棒者：${t.handoffToPerson}`
          : `值 ${t.days} 天（${why}）提早交棒（暫無可接棒人員）`;
      } else if (t.reason === 'inProgress') {
        statusLine = `已值 ${t.days} 天（模擬範圍結束，尚未滿 5 天）`;
      }

      const handoffBadge = t.cameFromHandoff
        ? `<div class="timeline-card__handoff-in">🔁 接棒自：${t.handoffFromPerson}</div>` : '';

      return `
        <div class="timeline-card ${reasonClass}">
          <div class="timeline-card__no">第 ${t.no} 棒</div>
          <div class="timeline-card__person">${t.person}</div>
          <div class="timeline-card__range">${t.startDate} ～ ${t.endDate}</div>
          <div class="timeline-card__status">${statusLine}</div>
          ${handoffBadge}
        </div>
        <div class="timeline-arrow">➔</div>`;
    }).join('');

    const skippedHtml = data.skippedTurns.length ? `
      <div class="timeline-skipped">
        <div class="timeline-skipped__title">⏭️ 順位跳過紀錄（未獲選為當次接棒者）</div>
        ${data.skippedTurns.map(s => `<div class="timeline-skipped__item">${s.date}：${s.person}（${s.reason}）</div>`).join('')}
      </div>` : '';

    return `
      <div class="timeline-track">
        <div class="timeline-track__title">
          <span class="shift-badge shift-badge--${st}"><span class="shift-code">${st}</span>${SHIFT_LABELS[st]}</span>
          輪值序列推演
        </div>
        <div class="timeline-cards">${cardsHtml}</div>
        ${skippedHtml}
      </div>`;
  }).join('');
}

/* ----------------------------------------------------------------------------
 * 十三、統一渲染入口 + 事件綁定
 * --------------------------------------------------------------------------*/

function renderAll() {
  renderValidationBar();
  renderToolbar();
  renderLeavePanel();
  renderCalendar();
  renderStats();
  renderTimeline();
}

function attachEventListeners() {
  document.getElementById('monthTabs').addEventListener('click', e => {
    const btn = e.target.closest('[data-month]');
    if (!btn) return;
    state.currentMonth = btn.dataset.month;
    renderToolbar();
    renderCalendar();
    renderStats();
  });

  document.getElementById('shiftTabs').addEventListener('click', e => {
    const btn = e.target.closest('[data-shift]');
    if (!btn) return;
    state.currentShift = btn.dataset.shift;
    renderToolbar();
    renderCalendar();
    renderStats();
    renderTimeline();
  });

  document.getElementById('resetBtn').addEventListener('click', resetToDefaults);

  document.getElementById('leaveForm').addEventListener('submit', e => {
    e.preventDefault();
    const name = document.getElementById('leaveNameSelect').value;
    const start = document.getElementById('leaveStartInput').value;
    const end = document.getElementById('leaveEndInput').value;
    const note = document.getElementById('leaveNoteInput').value.trim();

    if (!name || !start || !end) {
      window.alert('請完整填寫同仁姓名、預假起始日期與結束日期。');
      return;
    }
    if (start > end) {
      window.alert('預假結束日期不可早於起始日期。');
      return;
    }

    leaveRecords.push({
      id: `leave-${Date.now()}-${Math.random().toString(36).slice(2, 7)}`,
      name, start, end, note
    });

    saveToStorage();
    recomputeSchedule();
    renderAll();
    e.target.reset();
  });

  document.getElementById('leaveList').addEventListener('click', e => {
    const btn = e.target.closest('[data-del-id]');
    if (!btn) return;
    leaveRecords = leaveRecords.filter(r => r.id !== btn.dataset.delId);
    saveToStorage();
    recomputeSchedule();
    renderAll();
  });

  SHIFT_TYPES.forEach(st => {
    const sel = document.getElementById(`offsetSelect-${st}`);
    if (!sel) return;
    sel.addEventListener('change', () => {
      shiftStartIndex[st] = Number(sel.value);
      saveToStorage();
      recomputeSchedule();
      renderAll();
    });
  });
}

/* ----------------------------------------------------------------------------
 * 十四、初始化
 * --------------------------------------------------------------------------*/

document.addEventListener('DOMContentLoaded', () => {
  loadFromStorage();
  recomputeSchedule();
  attachEventListeners();
  renderAll();
});
