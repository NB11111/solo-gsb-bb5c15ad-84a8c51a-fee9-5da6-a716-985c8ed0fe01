// 跨演员口令依赖
// 在两条到位口令之间维护有向约束：
//   前置口令完成（当前模式下实际到达 + 停留时长）后，至少等待 waitSeconds 秒，
//   为执行后置口令而实际出发（以该口令为终点的区段出发）才可发生，即
//     前置完成时刻 + waitSeconds ≤ 后置口令的实际出发时刻。
// 保存（新增依赖）前检查整张依赖图：成环则拒绝写入，并返回构成环的口令链。
// 校验时任一端口令在当前模式下不可达（或已被删除、无法取到实际时刻），标为「无法判定」。

/** 最小等待秒数上限（1 小时） */
const MAX_WAIT_SECONDS = 3600;

const UNKNOWN_REASON_TEXT = {
  'pre-unreachable': '前置口令在当前模式下不可达，实际完成时刻未知',
  'post-unreachable': '后置口令在当前模式下不可达，实际出发时刻未知',
  missing: '依赖的口令已被删除',
};

/** 构造一条依赖（仅规整字段，不做业务校验） */
function normalizeDependency(dep) {
  return {
    id: dep.id,
    preCueId: dep.preCueId,
    postCueId: dep.postCueId,
    waitSeconds: dep.waitSeconds,
  };
}

/**
 * 在「整图 + 一条候选边」上做环检测，返回构成环的口令 ID 链（首尾不同 ID，
 * 已按环顺序排列，如 [A, B, C] 表示 A→B→C→A）；无环返回 null。
 * @param {Array} dependencies 已有依赖
 * @param {{preCueId: string, postCueId: string}} [candidate] 待新增的边；省略时仅检查整图
 */
function findCycle(dependencies, candidate) {
  const adj = new Map();
  const addEdge = (u, v) => {
    if (!adj.has(u)) adj.set(u, []);
    adj.get(u).push(v);
  };
  for (const d of dependencies) addEdge(d.preCueId, d.postCueId);
  if (candidate) addEdge(candidate.preCueId, candidate.postCueId);

  const WHITE = 0; // 未访问
  const GRAY = 1; // 在当前递归栈中
  const BLACK = 2; // 已完成
  const color = new Map();
  const stack = []; // 当前递归栈（节点 + 下一条待访问出边下标）
  let cycle = null;

  for (const start of adj.keys()) {
    if (cycle) break;
    if ((color.get(start) || WHITE) !== WHITE) continue;
    color.set(start, GRAY);
    stack.push({ node: start, idx: 0 });

    while (stack.length > 0 && !cycle) {
      const top = stack[stack.length - 1];
      const nexts = adj.get(top.node) || [];
      if (top.idx >= nexts.length) {
        color.set(top.node, BLACK);
        stack.pop();
        continue;
      }
      const next = nexts[top.idx++];
      const c = color.get(next) || WHITE;
      if (c === GRAY) {
        // 从栈中 next 的位置起即构成环
        const at = stack.findIndex((f) => f.node === next);
        cycle = stack.slice(at).map((f) => f.node);
      } else if (c === WHITE) {
        color.set(next, GRAY);
        stack.push({ node: next, idx: 0 });
      }
    }
  }
  return cycle;
}

/** 口令展示标签：演员名 · mm:ss · 区域名 */
function cueLabel(cueId, cueIndex) {
  const c = cueIndex && cueIndex.get(cueId);
  if (!c) return `（已删除口令 ${cueId}）`;
  return `${c.actorName} · ${fmtTime(c.time)} · ${c.areaName}`;
}

function fmtTime(sec) {
  const abs = Math.abs(sec);
  const m = Math.floor(abs / 60);
  const s = abs % 60;
  return `${String(m).padStart(2, '0')}:${String(s).padStart(2, '0')}`;
}

/**
 * 把环的口令 ID 链渲染为可读文本，并在末尾接回环起点以呈现闭环。
 * @param {Array<string>} cycle findCycle 返回的环链
 * @param {Map} cueIndex cueId → { cue, actorName, areaName }
 */
function cycleChainText(cycle, cueIndex) {
  const ids = [...cycle, cycle[0]];
  return ids.map((id) => cueLabel(id, cueIndex)).join(' → ');
}

/**
 * 评估全部跨演员口令依赖。
 * @param {Array} dependencies 依赖列表 [{ id, preCueId, postCueId, waitSeconds }]
 * @param {Map} cueIndex 口令时间索引：
 *   cueId → { cue, actorId, actorName, areaName, time, arrival, depart, reachable }
 *   arrival：当前模式实际到达该口令的时刻（首条口令视为准时，= 计划时刻）；
 *   depart：为执行该口令实际出发的时刻（以该口令为终点的区段出发；首条口令为计划时刻）；
 *   reachable=false 表示该口令在当前模式下不可达（任一端不可达则无法判定）。
 * @returns {{ total, satisfied, violated, unknown, items }}
 *   items[i]：{ id, preCueId, postCueId, waitSeconds, status,
 *               preFinish, postDepart, earliestAllowed, diffSeconds,
 *               pre/post 描述, reason }
 *   diffSeconds = 后置实际出发 - 最早允许出发；满足时为富余秒数，违约时为负的缺口秒数。
 */
function evaluateDependencies(dependencies, cueIndex) {
  const items = [];
  let satisfied = 0;
  let violated = 0;
  let unknown = 0;

  for (const d of dependencies) {
    const pre = cueIndex.get(d.preCueId);
    const post = cueIndex.get(d.postCueId);

    const describe = (c) =>
      c
        ? {
            cueId: c.cue.id,
            actorId: c.actorId,
            actorName: c.actorName,
            areaName: c.areaName,
            time: c.time,
            note: c.cue.note || '',
          }
        : { cueId: null, actorId: null, actorName: '（已删除口令）', areaName: '—', time: null, note: '' };

    const item = {
      id: d.id,
      preCueId: d.preCueId,
      postCueId: d.postCueId,
      waitSeconds: d.waitSeconds,
      pre: describe(pre),
      post: describe(post),
      preFinish: null,
      postDepart: null,
      earliestAllowed: null,
      diffSeconds: null,
      status: 'unknown',
      reason: null,
    };

    if (!pre) {
      item.reason = 'missing';
    } else if (!pre.reachable) {
      item.reason = 'pre-unreachable';
    } else if (!post) {
      item.reason = 'missing';
    } else if (!post.reachable) {
      item.reason = 'post-unreachable';
    } else {
      // 前置完成 = 实际到达 + 停留时长；停留时长在两种模式下均计入完成时刻
      item.preFinish = pre.arrival + (Number.isInteger(pre.cue.dwell) && pre.cue.dwell > 0 ? pre.cue.dwell : 0);
      item.postDepart = post.depart;
      item.earliestAllowed = item.preFinish + d.waitSeconds;
      item.diffSeconds = item.postDepart - item.earliestAllowed;
      item.status = item.diffSeconds >= 0 ? 'satisfied' : 'violated';
    }

    if (item.status === 'satisfied') satisfied++;
    else if (item.status === 'violated') violated++;
    else unknown++;

    items.push(item);
  }

  // 稳定排序：前置演员 → 前置时刻 → 后置演员 → 后置时刻（删除项排末尾）
  items.sort((x, y) => {
    const ax = x.pre.actorName || '';
    const ay = y.pre.actorName || '';
    return (
      ax.localeCompare(ay, 'zh') ||
      (x.pre.time === null ? 1 : 0) - (y.pre.time === null ? 1 : 0) ||
      (x.pre.time || 0) - (y.pre.time || 0) ||
      (x.post.actorName || '').localeCompare(y.post.actorName || '', 'zh') ||
      (x.post.time || 0) - (y.post.time || 0)
    );
  });

  return { total: items.length, satisfied, violated, unknown, items };
}

module.exports = {
  MAX_WAIT_SECONDS,
  UNKNOWN_REASON_TEXT,
  normalizeDependency,
  findCycle,
  evaluateDependencies,
  cueLabel,
  cycleChainText,
  fmtTime,
};
