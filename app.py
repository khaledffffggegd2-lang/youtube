"""
كورة لايف — موقع كورة + توقعات حية. ملف واحد بس: app.py (السيرفر + المحرك + الواجهة + PWA).

التشغيل:   python app.py     وبعدها افتح http://localhost:5000 في المتصفح.
المطلوب:   مكتبة requests بس (موجودة عندك).

كله في الذاكرة، ماعدا سجل دقة التوقعات بيتحفظ في track.json جنب الملف.
"""
import json
import math
import os
import re
import sys
import threading
import time
import traceback
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
PORT = int(os.environ.get("PORT", "5000"))
FIX = os.environ.get("FIXTURES")                     # للتجربة بدون إنترنت بس (مش محتاجه)
CAIRO = timezone(timedelta(hours=3))
TOP_COMPS = {"75", "65", "77", "67", "68", "64", "70", "60"}
PIN_ORDER = ["60", "65", "75", "77", "67", "68"]      # دوري الأبطال والدوريات الكبيرة الأول
STANDINGS = [("الدوري المصري", "egypt/premier-league"), ("الدوري السعودي", "saudi-arabia/pro-league"),
             ("الدوري الإنجليزي", "england/premier-league"), ("الدوري الإسباني", "spain/laliga"),
             ("الدوري الإيطالي", "italy/serie-a"), ("الدوري الألماني", "germany/bundesliga"),
             ("الدوري الفرنسي", "france/ligue-1")]


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


def today():
    return datetime.now(CAIRO).strftime("%Y%m%d")


# ====================================================================
#  1) محرك ما قبل الماتش: Poisson + Dixon-Coles + قوة الفرق من الجدول
# ====================================================================
HALF_LIFE_DAYS, FRIENDLY_W, UNKNOWN_OPP_W = 60, 0.35, 0.6
K_RECENT, HOME_SPLIT_W, RHO, MAX_GOALS = 3.0, 0.25, -0.06, 10
K_1X2, K_GOALS, GOALS_SCALE, FH_SHARE = 4.0, 20.0, 1.05, 0.42   # من الاختبار الرجعي (165 ماتش، 5 دوريات)


def norm(s):
    return str(s).lower().strip()


def parse_date(s):
    return datetime.strptime(str(s)[:8], "%Y%m%d")


class League:
    """متوسطات الدوري وقوة كل فريق من جدول الترتيب (لو مفيش جدول: متوسطات عامة)."""

    def __init__(self, data=None):
        self.teams, self.games, self.LH, self.LA = {}, 0, 1.45, 1.15
        try:
            tabs = {t["LTT"]: t["team"] for t in data["LeagueTable"]["L"][0]["Tables"]}
            by = lambda lst: {norm(t["Tnm"]): t for t in lst}
            tot = by(tabs[1])
            home, away = (by(tabs[2]) if 2 in tabs else tot), (by(tabs[3]) if 3 in tabs else tot)
            self.LH = sum(t["gf"] for t in home.values()) / sum(t["pld"] for t in home.values())
            self.LA = sum(t["gf"] for t in away.values()) / sum(t["pld"] for t in away.values())
            self.teams = {n: {"tot": tot[n], "home": home.get(n), "away": away.get(n)} for n in tot}
            self.games = sum(t["pld"] for t in tot.values()) / 2
        except Exception:  # noqa: BLE001  (دوري من غير جدول أو بداية موسم)
            self.teams, self.games, self.LH, self.LA = {}, 0, 1.45, 1.15
        self.avg = (self.LH + self.LA) / 2

    def overall(self, name, K):
        e = self.teams.get(norm(name))
        if not e:
            return 1.0, 1.0, False
        t, a = e["tot"], self.avg
        return ((t["gf"] + K * a) / (t["pld"] + K)) / a, ((t["ga"] + K * a) / (t["pld"] + K)) / a, True

    def season(self, name, venue, K):
        e = self.teams.get(norm(name))
        if not e:
            return 1.0, 1.0
        ao, do, _ = self.overall(name, K)
        s = e["home"] if venue == "home" else e["away"]
        if not s or s["pld"] == 0:
            return ao, do
        sf, sa = (self.LH, self.LA) if venue == "home" else (self.LA, self.LH)
        av = ((s["gf"] + K * sf) / (s["pld"] + K)) / sf
        dv = ((s["ga"] + K * sa) / (s["pld"] + K)) / sa
        return (1 - HOME_SPLIT_W) * ao + HOME_SPLIT_W * av, (1 - HOME_SPLIT_W) * do + HOME_SPLIT_W * dv

    def info(self, name):
        e = self.teams.get(norm(name))
        return e["tot"] if e else None


def flatten(blocks):
    out = []
    for b in blocks or []:
        friendly = "friendl" in str((b.get("stage") or {}).get("stageName", "")).lower()
        for e in b.get("events", []):
            if e.get("statusCode") != "FT":
                continue
            try:
                out.append({"date": parse_date(e["startDateTimeString"]), "home": e["homeName"], "away": e["awayName"],
                            "hg": int(e["homeScore"]), "ag": int(e["awayScore"]), "friendly": friendly})
            except (KeyError, ValueError):
                continue
    return out


def team_rating(team, venue, matches, league, ref, K):
    att_s, def_s = league.season(team, venue, K)
    sw = s_att = s_def = 0.0
    for m in matches:
        w = 0.5 ** (max((ref - m["date"]).days, 0) / HALF_LIFE_DAYS) * (FRIENDLY_W if m["friendly"] else 1)
        if norm(m["home"]) == norm(team):
            gf, ga, opp, bf, ba = m["hg"], m["ag"], m["away"], league.LH, league.LA
        elif norm(m["away"]) == norm(team):
            gf, ga, opp, bf, ba = m["ag"], m["hg"], m["home"], league.LA, league.LH
        else:
            continue
        oa, od, known = league.overall(opp, K)
        w *= 1 if known else UNKNOWN_OPP_W
        s_att += w * gf / (bf * od)
        s_def += w * ga / (ba * oa)
        sw += w
    if not sw:
        return {"att": att_s, "def": def_s, "recent_weight": 0.0}
    ar, dr = s_att / sw, s_def / sw
    return {"att": (sw * ar + K_RECENT * att_s) / (sw + K_RECENT), "def": (sw * dr + K_RECENT * def_s) / (sw + K_RECENT),
            "recent_weight": sw}


def pmf(k, lam):
    return math.exp(-lam) * lam ** k / math.factorial(k) if lam > 0 else (1.0 if k == 0 else 0.0)


def score_matrix(lh, la):
    def tau(i, j):
        if i == 0 and j == 0: return 1 - lh * la * RHO
        if i == 0 and j == 1: return 1 + lh * RHO
        if i == 1 and j == 0: return 1 + la * RHO
        if i == 1 and j == 1: return 1 - RHO
        return 1.0
    m = [[pmf(i, lh) * pmf(j, la) * tau(i, j) for j in range(MAX_GOALS + 1)] for i in range(MAX_GOALS + 1)]
    t = sum(map(sum, m))
    return [[x / t for x in r] for r in m]


def markets(m):
    n = len(m)
    H = sum(m[i][j] for i in range(n) for j in range(n) if i > j)
    D = sum(m[i][i] for i in range(n))
    over = lambda t: sum(m[i][j] for i in range(n) for j in range(n) if i + j > t)
    return {"H": H, "D": D, "A": 1 - H - D, "btts": sum(m[i][j] for i in range(1, n) for j in range(1, n)),
            "o15": over(1.5), "o25": over(2.5), "o35": over(3.5)}


SHRINK = {"منخفضة": 0.12, "متوسطة": 0.06, "كويسة": 0.03}


def calib(h, d, a, conf):
    d *= 1 + 0.08 * (1 - abs(h - a))
    t = h + d + a
    h, d, a = h / t, d / t, a / t
    s = SHRINK[conf]
    return {"H": (1 - s) * h + s * 0.45, "D": (1 - s) * d + s * 0.27, "A": (1 - s) * a + s * 0.28}


def prematch(event, table_json):
    league = League(table_json)
    home, away = event["homeTeamName"], event["awayTeamName"]
    ref = parse_date(event["startDateTimeString"])
    hh = event.get("headToHead") or {}
    hm, am = flatten(hh.get("home")), flatten(hh.get("away"))

    def lam(K):
        hr, ar = team_rating(home, "home", hm, league, ref, K), team_rating(away, "away", am, league, ref, K)
        return league.LH * hr["att"] * ar["def"], league.LA * ar["att"] * hr["def"], hr, ar

    clip = lambda x: min(max(x, 0.2), 4.0)
    lh1, la1, hr, ar = lam(K_1X2)
    lh2, la2, _, _ = lam(K_GOALS)
    lh1, la1 = clip(lh1), clip(la1)
    lh2, la2 = clip(lh2 * GOALS_SCALE), clip(la2 * GOALS_SCALE)
    sm1 = score_matrix(lh1, la1)
    m1, m2 = markets(sm1), markets(score_matrix(lh2, la2))
    lam_fh = (lh2 + la2) * FH_SHARE
    p0 = math.exp(-lam_fh)
    cells = sorted(((i, j, p) for i, r in enumerate(sm1) for j, p in enumerate(r)), key=lambda c: -c[2])[:5]
    w = min(hr["recent_weight"], ar["recent_weight"])
    conf = "منخفضة" if (league.games < 40 or w < 2) else ("متوسطة" if w < 4 else "كويسة")
    x1 = calib(m1["H"], m1["D"], m1["A"], conf)
    return {
        "computed_at": int(time.time()), "lh1": lh1, "la1": la1, "lh2": lh2, "la2": la2,
        "xg": {"home": round(lh2, 2), "away": round(la2, 2)},
        "x1x2": x1,
        "double": {"1X": x1["H"] + x1["D"], "X2": x1["A"] + x1["D"], "12": x1["H"] + x1["A"]},
        "btts": m2["btts"], "over": {"1.5": m2["o15"], "2.5": m2["o25"], "3.5": m2["o35"]},
        "fh": {"o05": 1 - p0, "o15": 1 - p0 - p0 * lam_fh},
        "top_scores": [(f"{i}-{j}", p) for i, j, p in cells],
        "confidence": conf,
    }


# ====================================================================
#  2) المحرك الحي: بيحدّث الاحتمالات حسب الدقيقة والنتيجة والكروت الحمرا
# ====================================================================
S1, S2 = 3.0, 6.0
END1, END2 = 45 + S1, 90 + S1 + S2
EDGES = [0, 15, 30, END1, END1 + 15, END1 + 30, END2]
SHARES = [0.117, 0.133, 0.169, 0.172, 0.153, 0.256]
RED_OWN, RED_OPP, MAXG = 0.75, 1.30, 12   # معايَرة من 52 ماتش فيهم كرت أحمر (±0.2)، وأقرب لدراسات الكرة


def pos(half, minute, extra=0):
    if half == 1:
        return min(min(minute, 45) + extra, END1 - 0.01)
    return min(END1 + (max(minute, 45) - 45) + extra, END2 - 0.01)


def remaining_fraction(p, until=END2):
    tot = 0.0
    for i, s in enumerate(SHARES):
        a, b = EDGES[i], EDGES[i + 1]
        lo, hi = max(a, p), min(b, until)
        if hi > lo:
            tot += s * (hi - lo) / (b - a)
    return tot


def live_markets(lh, la, p, score, reds, fh_goals=None):
    f = remaining_fraction(p)
    sh, sa = score
    rh = lh * f * RED_OWN ** reds[0] * RED_OPP ** reds[1]
    ra = la * f * RED_OWN ** reds[1] * RED_OPP ** reds[0]
    ph, pa = [pmf(k, rh) for k in range(MAXG + 1)], [pmf(k, ra) for k in range(MAXG + 1)]
    H = D = A = bt = 0.0
    ov = {1.5: 0.0, 2.5: 0.0, 3.5: 0.0}
    for i in range(MAXG + 1):
        for j in range(MAXG + 1):
            pr = ph[i] * pa[j]
            fh, fa = sh + i, sa + j
            if fh > fa: H += pr
            elif fh == fa: D += pr
            else: A += pr
            if fh and fa: bt += pr
            for t in ov:
                if fh + fa > t: ov[t] += pr
    tot = H + D + A
    out = {"H": H / tot, "D": D / tot, "A": A / tot, "btts": bt / tot, "o15": ov[1.5] / tot, "o25": ov[2.5] / tot,
           "o35": ov[3.5] / tot}
    if fh_goals is not None and p < END1:
        lam = (lh * RED_OWN ** reds[0] * RED_OPP ** reds[1] + la * RED_OWN ** reds[1] * RED_OPP ** reds[0]) * remaining_fraction(p, END1)
        for t, key in ((0.5, "fh05"), (1.5, "fh15")):
            need = int(t - fh_goals) + 1
            out[key] = 1.0 if need <= 0 else 1 - sum(pmf(k, lam) for k in range(need))
    return out


# ====================================================================
#  3) ربط المحركين بالبيانات: الأحداث، الحالة، الاحتمالات الحية، أفضل اختيار
# ====================================================================
GOAL_KINDS = {"FootballGoal": "goal", "FootballGoalPen": "pen_goal", "FootballOwnGoal": "own_goal", "FootballPenaltyGoal": "pen_goal"}
OTHER_KINDS = {"FootballYellowCard": "yellow", "FootballRedCard": "red", "FootballRedYellowCard": "second_yellow",
               "FootballGoalMiss": "goal_cancelled", "FootballGoalPenMiss": "pen_miss"}


def _minute(t):
    nums = [int(x) for x in re.findall(r"\d+", str(t))]
    return (nums[0], nums[1] if len(nums) > 1 else 0) if nums else (None, 0)


def parse_incidents(event):
    out = []
    for period, by_min in ((event.get("incidents") or {}).get("incs") or {}).items():
        half = 1 if str(period).endswith("1") else 2
        for groups in by_min.values():
            for g in groups:
                for side in ("HOME", "AWAY"):
                    for it in g.get(side, []):
                        typ = it.get("type", "")
                        kind = GOAL_KINDS.get(typ) or OTHER_KINDS.get(typ) or ("sub" if "Subst" in typ else None)
                        if not kind:
                            continue
                        mn, ex = _minute(it.get("time"))
                        a = it.get("assist") or []
                        out.append({"min": mn, "extra": ex, "half": half, "side": side.lower(), "kind": kind,
                                    "player": it.get("name"), "assist": a[0].get("name") if a else None,
                                    "score": it.get("score"), "var": it.get("varLabel")})
    out.sort(key=lambda r: (r["half"], r["min"] or 0, r["extra"]))
    return out


def live_state(event, inc):
    det = (event.get("scores") or {}).get("matchStatusDetails") or {}
    try:
        score = (int(event.get("homeTeamScore") or 0), int(event.get("awayTeamScore") or 0))
    except ValueError:
        score = (0, 0)
    reds = [0, 0]
    for i in inc:
        if i["kind"] in ("red", "second_yellow"):
            reds[0 if i["side"] == "home" else 1] += 1
    status, lt = det.get("status") or "", det.get("liveTime") or ""
    fin, started = bool(det.get("isFinished")), not det.get("isNotStarted", True)
    mn, ex = _minute(lt)
    if fin:
        p = END2
    elif not started:
        p = 0.0
    elif ("half" in status.lower() and "time" in status.lower()) or lt.upper().startswith("HT"):
        p = END1
    elif mn is None:
        p = None
    else:
        p = pos(2 if mn > 45 else 1, mn, ex)
    return {"score": score, "reds": tuple(reds), "pos": p, "finished": fin, "started": started, "live_time": lt}


def live_probs(pre, st, fh_goals=None):
    if st["pos"] is None or st["finished"] or not st["started"]:
        return None
    a = live_markets(pre["lh1"], pre["la1"], st["pos"], st["score"], st["reds"])
    b = live_markets(pre["lh2"], pre["la2"], st["pos"], st["score"], st["reds"], fh_goals)
    out = {"x1x2": {"H": a["H"], "D": a["D"], "A": a["A"]}, "btts": b["btts"],
           "over": {"1.5": b["o15"], "2.5": b["o25"], "3.5": b["o35"]}}
    if "fh05" in b:
        out["fh"] = {"o05": b["fh05"], "o15": b["fh15"]}
    return out


def best_picks(home, away, x, btts, over, n=2):
    H, D, A_ = x["H"], x["D"], x["A"]
    c = [(f"فوز {home}", H, 1, "H"), (f"فوز {away}", A_, 1, "A"), (f"{home} أو تعادل", H + D, 1, "1X"), (f"{away} أو تعادل", A_ + D, 1, "X2"),
         ("أكتر من 1.5 هدف", over["1.5"], 0, "o15"), ("أكتر من 2.5 هدف", over["2.5"], 0, "o25"), ("أقل من 2.5 هدف", 1 - over["2.5"], 0, "u25"),
         ("أقل من 3.5 هدف", 1 - over["3.5"], 0, "u35"), ("كلا الفريقين يسجل", btts, 0, "bt"), ("كلا الفريقين مايسجلش", 1 - btts, 0, "nb")]
    ok = sorted((t for t in c if 0.50 <= t[1] <= 0.80), key=lambda t: -(t[1] * (1.0 if t[2] else 0.93)))
    out = []
    for l, p, k, key in ok:
        if k and out and out[0]["proven"] and "أو تعادل" in l and "أو تعادل" in out[0]["label"]:
            continue
        out.append({"label": l, "p": round(p, 4), "odds": round(1 / p, 2), "min_odds": round(1.05 / p, 2), "k": key, "proven": bool(k),
                    "grade": "قوية" if p >= 0.66 else ("كويسة" if p >= 0.58 else "ضعيفة")})
        if len(out) == n:
            break
    return out


# ====================================================================
#  4) المصدر: LiveScore (API غير رسمي) + كاش قصير في الذاكرة
# ====================================================================
PUBLIC = "https://prod-cdn-public-api.lsmedia1.com"
MEV = "https://prod-cdn-mev-api.lsmedia1.com"
HEADERS = {"User-Agent": "Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Mobile Safari/537.36",
           "Origin": "https://www.livescore.com", "Referer": "https://www.livescore.com/", "Accept-Language": "en-US,en;q=0.9"}
FALLBACK_BUILD, MIN_GAP = "SjiIpLYkI-fb8A7fnzR-Q", 0.25
FINISHED = {"FT", "AET", "AP", "Pen.", "Pen", "FT_PEN"}


def slugify(name):
    return re.sub(r"[^a-z0-9]+", "-", str(name).lower().replace("&", "and")).strip("-")


def norm_status(eps):
    e = str(eps or "")
    if e in ("NS", ""): return "NS", None
    if e in FINISHED or e.startswith("FT") or e.startswith("AET"): return "FT", None
    if e == "HT": return "HT", None
    if e in ("Postp.", "Canc.", "Aband.", "Susp.", "Int."): return "OFF", None
    return "LIVE", e


def parse_daily(data):
    out = []
    for sec in (data or {}).get("Sctns", []):
        ts = sec.get("Ts")
        for t in ([ts] if isinstance(ts, dict) else ts or []):
            for e in t.get("Evs", []):
                try:
                    h, a = e["T1"][0], e["T2"][0]
                except (KeyError, IndexError):
                    continue
                st, minute = norm_status(e.get("Eps"))
                country, comp = t.get("Ccd") or t.get("CnmT") or "", t.get("Scd") or t.get("CompUrlNm") or ""
                out.append({
                    "eid": str(e["Eid"]), "status": st, "minute": minute, "kickoff": e.get("Est"),
                    "hs": e.get("Tr1"), "as": e.get("Tr2"), "home": h.get("Nm"), "away": a.get("Nm"),
                    "home_id": h.get("ID"), "away_id": a.get("ID"), "home_img": h.get("Img"), "away_img": a.get("Img"),
                    "home_color": h.get("Fc"), "away_color": a.get("Fc"),
                    "league": t.get("Snm"), "country_name": t.get("Cnm"), "comp_id": t.get("CompId"),
                    "league_badge": t.get("BdgUrl"), "country": country, "comp": comp,
                    "path": f"{country}/{comp}/{slugify(h.get('Nm'))}-vs-{slugify(a.get('Nm'))}/{e['Eid']}"})
    return out


class Source:
    def __init__(self):
        self.s, self.cache, self.lock = requests.Session(), {}, threading.Lock()
        self.last, self.build, self.build_ts = 0.0, None, 0.0
        self.info, self.day_mode, self.live_fail, self.imgs = {}, None, 0, None

    def _throttle(self):
        with self.lock:
            w = MIN_GAP - (time.time() - self.last)
            if w > 0:
                time.sleep(w)
            self.last = time.time()

    def _cached(self, key, ttl, fn):
        now, hit = time.time(), self.cache.get(key)
        if hit and now - hit[0] < (ttl(hit[1]) if callable(ttl) else ttl):
            return hit[1]
        try:
            val = fn()
        except Exception:
            if hit:                    # لو السحب فشل نرجّع آخر نسخة بدل ما نكسر الصفحة
                return hit[1]
            raise
        self.cache[key] = (now, val)
        return val

    def _fix(self, name):
        with open(os.path.join(FIX, name), encoding="utf-8") as f:
            return json.load(f)

    def _get(self, url, params=None, headers=None):
        self._throttle()
        r = self.s.get(url, params=params, headers={**HEADERS, **(headers or {})}, timeout=20)
        r.raise_for_status()
        return r.json()

    def build_id(self, force=False):
        if self.build and not force and time.time() - self.build_ts < 3600:
            return self.build
        try:
            self._throttle()
            r = self.s.get("https://www.livescore.com/en/football/", headers=HEADERS, timeout=20)
            m = re.search(r'"buildId":"([^"]+)"', r.text)
            if m:
                self.build, self.build_ts = m.group(1), time.time()
                return self.build
        except requests.RequestException:
            pass
        self.build = self.build or FALLBACK_BUILD
        return self.build

    def next_data(self, path, tab=""):
        country, comp, slug, eid = path.split("/")
        params = {"sport": "football", "dateOrCategory": country, "competitionOrStage": comp,
                  "stageOrMatchName": slug, "eventId": eid}
        hdr = {"x-nextjs-data": "1", "referer": f"https://www.livescore.com/en/football/{path}/"}
        for attempt in (0, 1):
            url = f"https://www.livescore.com/_next/data/{self.build_id(force=bool(attempt))}/en/football/{path}{'/' + tab if tab else ''}.json"
            self._throttle()
            r = self.s.get(url, params=params, headers={**HEADERS, **hdr}, timeout=20)
            if r.status_code == 404 and attempt == 0:
                continue
            r.raise_for_status()
            return r.json()

    def _day_raw(self, date, loc="en"):
        """بيجرّب أكتر من طريقة عشان ييجي كل الدوريات مش أول صفحة بس."""
        base = f"{MEV}/api/v2/date/soccer/{date}/3"
        tries = [("paging", {"paging": "true", "direction": "down", "locale": loc}), ("full", {"locale": loc})]
        if self.day_mode:
            tries = [t for t in tries if t[0] == self.day_mode] or tries
        best = None
        for name, params in tries:
            try:
                d = self._get(base, params)
            except Exception as e:  # noqa: BLE001
                self.info[f"day_{name}"] = f"فشل: {repr(e)[:80]}"
                continue
            n = sum(len([t] if isinstance(t, dict) else t or []) for t in (s.get("Ts") for s in d.get("Sctns", [])))
            self.info[f"day_{name}"] = f"{n} دوري"
            if best is None or n > best[0]:
                best = (n, d, name)
        if best is None:
            raise RuntimeError("مقدرتش أجيب قايمة الماتشات")
        d = best[1]
        if len(tries) == 2:
            self.day_mode = best[2]
        if best[2] == "paging" and (d.get("Nav") or {}).get("Hn") and d.get("Ts"):
            seen, ts = {str((s.get("Ts") or {}).get("Sid")) for s in d["Sctns"]}, d["Ts"]
            for _ in range(8):
                try:
                    nx = self._get(base, {"paging": "true", "direction": "down", "locale": loc, "ts": ts})
                except Exception as e:  # noqa: BLE001
                    self.info["day_next"] = f"فشل: {repr(e)[:80]}"
                    break
                new = [s for s in nx.get("Sctns", []) if str((s.get("Ts") or {}).get("Sid")) not in seen]
                if not new:
                    break
                self.info["day_next"] = "شغال"
                for s in new:
                    seen.add(str((s.get("Ts") or {}).get("Sid")))
                d["Sctns"].extend(new)
                if not (nx.get("Nav") or {}).get("Hn") or not nx.get("Ts"):
                    break
                ts = nx["Ts"]
        return d

    def daily(self, date, loc="en"):
        def run():
            if FIX:
                return self._fix("daily.json")
            return self._day_raw(date, loc)
        return self._cached(("daily", date, loc), 15 if loc == "en" else 1800, run)

    def live_all(self):
        if FIX or self.live_fail >= 2:
            return None
        try:
            d = self._cached(("live",), 10, lambda: self._get(f"{MEV}/api/v2/live/soccer/3", {"locale": "en"}))
            self.info["live_api"] = "شغال"
            return d
        except Exception as e:  # noqa: BLE001
            self.live_fail += 1
            self.info["live_api"] = f"فشل: {repr(e)[:80]}"
            return None

    def event_page(self, path, tab="", ttl=30):
        def run():
            if FIX:
                eid = path.split("/")[-1]
                for name in {"": [f"match_{eid}.json", f"h2h_{eid}.json"], "h2h": [f"h2h_{eid}.json"], "stats": ["stats.json"]}.get(tab, []):
                    if os.path.exists(os.path.join(FIX, name)):
                        return self._fix(name)
                raise FileNotFoundError(f"fixture {tab or 'summary'} {eid}")
            return self.next_data(path, tab)
        return self._cached(("ev", path, tab), ttl, run)

    def lineups(self, eid, ttl=120):
        return self._cached(("lu", eid), ttl, lambda: self._fix("lineups.json") if FIX else
                            self._get(f"{PUBLIC}/v1/api/app/lineups/soccer/{eid}", {"locale": "en"}))

    def table(self, country, league, ttl=600):
        return self._cached(("table", country, league), ttl, lambda: self._fix("table_spain_laliga.json") if FIX else
                            self._get(f"{PUBLIC}/v1/api/app/leagueTable-s/soccer/{country}/{league}", {"locale": "en"}))

    def image_bases(self):
        """بيكتشف أنهي عنوان لصور الشعارات شغال (مرة واحدة)."""
        if self.imgs:
            return self.imgs
        team = ["https://lsm-static-prod.livescore.com/medium/", "https://lsm-static-prod.livescore.com/high/",
                "https://storage.livescore.com/images/team/medium/", "https://storage.livescore.com/images/team/high/",
                "https://storage.lsmedia1.com/images/"]
        comp = ["https://storage.livescore.com/images/competition/medium/", "https://storage.livescore.com/images/competition/high/",
                "https://lsm-static-prod.livescore.com/medium/", "https://storage.lsmedia1.com/images/"]

        def ok(url):
            try:
                r = self.s.get(url, headers=HEADERS, timeout=6, stream=True)
                good = r.status_code == 200 and "image" in r.headers.get("content-type", "")
                r.close()
                return good
            except requests.RequestException:
                return False
        out = {"team": team, "comp": comp}
        if not FIX:
            for k, sample, lst in (("team", "enet/9783.png", team), ("comp", "2023-spain-laliga.png", comp)):
                win = [b for b in lst if ok(b + sample)]
                out[k] = win + [b for b in lst if b not in win]
                self.info[f"img_{k}"] = win[0] if win else "مفيش عنوان اشتغل (هيظهر الحرف الأول)"
        self.imgs = out
        return out


src = Source()


# ====================================================================
#  5) حالة التطبيق + الشغّال الخلفي
# ====================================================================
PREDS, PRED_ERR, LIVEP, WATCH, OPEN, PATHS = {}, {}, {}, {}, {}, {}
INFLIGHT, EX, WAKE = set(), ThreadPoolExecutor(8), threading.Event()
TEAM_AR, COMP_AR, EID_AR = {}, {}, {}        # أسماء عربي (بتتجمع من رد locale=ar)


def arabize(ms):
    for m in ms:
        ar = EID_AR.get(m["eid"])
        m["home_ar"] = (ar[0] if ar else None) or TEAM_AR.get(str(m["home_id"]))
        m["away_ar"] = (ar[1] if ar else None) or TEAM_AR.get(str(m["away_id"]))
        c = COMP_AR.get(str(m["comp_id"]))
        m["league_ar"], m["country_ar"] = (c if c else (None, None))
    return ms


def merged_day(date):
    """ماتشات اليوم (بالإنجليزي للمسارات) + الأسماء العربي + الشغالة دلوقتي."""
    ms = {m["eid"]: m for m in parse_daily(src.daily(date))}
    try:
        for m in parse_daily(src.daily(date, "ar")):
            EID_AR[m["eid"]] = (m["home"], m["away"])
            TEAM_AR[str(m["home_id"])], TEAM_AR[str(m["away_id"])] = m["home"], m["away"]
            COMP_AR[str(m["comp_id"])] = (m["league"], m["country_name"])
    except Exception as e:  # noqa: BLE001
        log("أسماء عربي:", repr(e)[:80])
    if date in (today(), (datetime.now(CAIRO) - timedelta(days=1)).strftime("%Y%m%d")):
        lv = src.live_all()
        if lv:
            for m in parse_daily(lv):
                if m["status"] in ("LIVE", "HT"):
                    ms[m["eid"]] = m
    return arabize(list(ms.values()))


def get_pre(path, country, comp, force=False):
    eid = path.split("/")[-1]
    hit = PREDS.get(eid)
    if hit and time.time() - hit["computed_at"] < 3 * 3600 and not force:
        return hit
    if time.time() - PRED_ERR.get(eid, 0) < 120:
        return hit
    try:
        ev = src.event_page(path, "h2h", ttl=1800)["pageProps"]["initialEventData"]["event"]
        try:
            table = src.table(country, comp)
        except Exception:  # noqa: BLE001  (دوري من غير جدول)
            table = None
        PREDS[eid] = prematch(ev, table)
        PRED_ERR.pop(eid, None)
        return PREDS[eid]
    except Exception as e:  # noqa: BLE001
        PRED_ERR[eid] = time.time()
        log("توقع فشل", eid, repr(e)[:120])
        return hit


def summary(path):
    def ttl(v):
        try:
            return 3600 if v["pageProps"]["initialEventData"]["event"]["scores"]["matchStatusDetails"].get("isFinished") else 10
        except (KeyError, TypeError):
            return 10
    return src.event_page(path, "", ttl=ttl)["pageProps"]["initialEventData"]["event"]


def fh_count(inc):
    return sum(1 for i in inc if i["half"] == 1 and i["kind"] in ("goal", "pen_goal", "own_goal"))


def update_live(m):
    pre = PREDS.get(m["eid"])
    if not pre:
        return
    ev = summary(m["path"])
    inc = parse_incidents(ev)
    st = live_state(ev, inc)
    lp = LIVEP[m["eid"]] = live_probs(pre, st, fh_count(inc))
    if lp and st["pos"] is not None:
        mn = st["pos"] if st["pos"] <= 45 else (45 if st["pos"] < END1 else st["pos"] - 3)
        x, h = lp["x1x2"], LIVEH.setdefault(m["eid"], [])
        row = [round(mn, 1), x["H"], x["D"], x["A"], st["score"][0], st["score"][1]]
        if not h or h[-1][4:] != row[4:] or row[0] - h[-1][0] >= 1:
            h.append(row)
            del h[:-300]


def get_pre_bg(m):
    """بيحسب التوقع في الخلفية من غير ما يحجز صفحة المستخدم."""
    eid = m["eid"]
    if eid in INFLIGHT or eid in PREDS:
        return
    INFLIGHT.add(eid)

    def run():
        try:
            get_pre(m["path"], m["country"], m["comp"])
            try:
                track_add(m)
            except Exception:  # noqa: BLE001
                pass
            if m["status"] in ("LIVE", "HT"):
                update_live(m)
        except Exception as e:  # noqa: BLE001
            log("bg", repr(e)[:100])
        finally:
            INFLIGHT.discard(eid)
    EX.submit(run)


def _safe_live(m):
    try:
        update_live(m)
    except Exception as e:  # noqa: BLE001
        log("تحديث حي فشل", m["eid"], repr(e)[:100])


TRACK_FILE = os.environ.get("TRACK_FILE", os.path.join(HERE, "track.json"))
TRACK, TLOCK, LIVEH, LAST_SETTLE = {}, threading.Lock(), {}, [0.0]
try:
    with open(TRACK_FILE, encoding="utf-8") as _f:
        TRACK.update(json.load(_f))
except Exception:  # noqa: BLE001
    pass


def track_save():
    try:
        with open(TRACK_FILE, "w", encoding="utf-8") as f:
            json.dump(TRACK, f, ensure_ascii=False)
    except Exception as e:  # noqa: BLE001
        log("track save", repr(e)[:80])


def track_add(m):
    eid, pre = m["eid"], PREDS.get(m["eid"])
    k = PATHS.get(eid) or m
    if not pre or eid in TRACK or k.get("status") != "NS" or not k.get("kickoff") or not k.get("home"):
        return
    home, away = k.get("home_ar") or k["home"], k.get("away_ar") or k["away"]
    x = pre["x1x2"]
    ps = best_picks(home, away, x, pre["btts"], pre["over"], 1)
    with TLOCK:
        TRACK[eid] = {"eid": eid, "path": k["path"], "home": home, "away": away, "league": k.get("league_ar") or k.get("league"),
                      "kick": float(k["kickoff"]), "x": [x["H"], x["D"], x["A"]],
                      "pick": {"label": ps[0]["label"], "p": ps[0]["p"], "k": ps[0]["k"]} if ps else None, "res": None}
        track_save()


def hit(k, hs, a):
    t = hs + a
    return {"H": hs > a, "A": a > hs, "1X": hs >= a, "X2": a >= hs, "o15": t > 1, "o25": t > 2, "u25": t < 3, "u35": t < 4,
            "bt": hs > 0 and a > 0, "nb": not (hs > 0 and a > 0)}[k]


def settle():
    now = time.time()
    if now - LAST_SETTLE[0] < 60:
        return
    LAST_SETTLE[0], n = now, 0
    for r in list(TRACK.values()):
        if r["res"] is not None or now < r["kick"] + 6600 or n >= 5:
            continue
        n += 1
        try:
            ev = summary(r["path"])
            st = live_state(ev, parse_incidents(ev))
            if st["finished"]:
                hs, a = st["score"]
                x = r["x"]
                o = [hs > a, hs == a, hs < a]
                r["res"] = {"s": [hs, a], "ok1": o.index(True) == x.index(max(x)), "brier": sum((x[i] - o[i]) ** 2 for i in range(3)),
                            "pk": hit(r["pick"]["k"], hs, a) if r["pick"] else None}
                with TLOCK:
                    track_save()
            elif now > r["kick"] + 86400:
                r["res"] = {"void": 1}
        except Exception as e:  # noqa: BLE001
            log("settle", repr(e)[:80])


def worker():
    """شغّال طول الوقت: يجدد القوايم، يحسب التوقعات بالتوازي، ويحدّث الماتشات الشغالة."""
    WATCH[today()] = time.time()
    while True:
        backlog = False
        try:
            now = time.time()
            for date, ts in list(WATCH.items()):
                if now - ts > 900 and date != today():
                    WATCH.pop(date, None)
                    continue
                ms = merged_day(date)
                for m in ms:
                    PATHS[m["eid"]] = m
                todo = [m for m in ms if m["status"] in ("NS", "LIVE", "HT") and m["eid"] not in PREDS
                        and m["eid"] not in INFLIGHT and time.time() - PRED_ERR.get(m["eid"], 0) > 120]
                todo.sort(key=lambda m: (m["status"] == "NS", str(m["comp_id"]) not in TOP_COMPS, m["kickoff"] or 0))
                for m in todo[:12]:
                    get_pre_bg(m)
                backlog = backlog or len(todo) > 12
                list(EX.map(_safe_live, [m for m in ms if m["status"] in ("LIVE", "HT") and m["eid"] in PREDS]))
            settle()
        except Exception:  # noqa: BLE001
            log("worker", traceback.format_exc()[-300:])
        WAKE.wait(2 if backlog else 10)
        WAKE.clear()


# ====================================================================
#  6) مساعدين + واجهات الـAPI
# ====================================================================
def league_key(m):
    cid = str(m["comp_id"])
    return (PIN_ORDER.index(cid) if cid in PIN_ORDER else 99, m["country_name"] or "", m["league"] or "")


def table_rows(tj):
    try:
        tabs = {t["LTT"]: t["team"] for t in tj["LeagueTable"]["L"][0]["Tables"]}
    except (KeyError, IndexError, TypeError):
        return []
    rows = [{"rnk": t.get("rnk"), "id": t.get("Tid"), "name": t.get("Tnm"), "name_ar": TEAM_AR.get(str(t.get("Tid"))),
             "pld": t.get("pld"), "w": t.get("win"), "d": t.get("drw"), "l": t.get("lst"), "gf": t.get("gf"),
             "ga": t.get("ga"), "gd": t.get("gd"), "pts": t.get("pts"), "img": t.get("Img")} for t in tabs.get(1, [])]
    return sorted(rows, key=lambda r: r["rnk"] or 99)


def simple_form(blocks, limit=6):
    out = []
    for b in blocks or []:
        for e in b.get("events", []):
            if e.get("statusCode") == "FT":
                out.append({"date": str(e.get("startDateTimeString", ""))[:8], "home": e.get("homeName"),
                            "away": e.get("awayName"), "hs": e.get("homeScore"), "as": e.get("awayScore")})
    return sorted(out, key=lambda r: r["date"], reverse=True)[:limit]


def status_of(st):
    if st["finished"]:
        return "FT"
    if not st["started"]:
        return "NS"
    return "HT" if st["pos"] is not None and abs(st["pos"] - END1) < 0.05 else "LIVE"


def pick_of(m):
    lp, pre = LIVEP.get(m["eid"]), PREDS.get(m["eid"])
    d = lp or pre
    if not d:
        return None
    ps = best_picks(m.get("home_ar") or m["home"], m.get("away_ar") or m["away"], d["x1x2"], d["btts"], d["over"])
    return {"best": ps[0], "alt": ps[1] if len(ps) > 1 else None, "live": bool(lp)} if ps else None


def demo_sim(ev, minute):
    """للتجربة بس (مع FIXTURES): يحاكي ماتش شغال في دقيقة معينة."""
    import copy
    base = src._fix("match_1810711.json")["pageProps"]["initialEventData"]["event"]
    incs, goals = copy.deepcopy(base["incidents"]), [0, 0]
    for period in incs["incs"].values():
        for key in list(period):
            nums = [int(x) for x in re.findall(r"\d+", key)]
            if (nums[0], nums[1] if len(nums) > 1 else 0) > (minute, 0):
                del period[key]
                continue
            for g in period[key]:
                for side, idx in (("HOME", 0), ("AWAY", 1)):
                    goals[idx] += sum(1 for it in g.get(side, []) if it.get("type") in ("FootballGoal", "FootballGoalPen"))
    ev = copy.deepcopy(ev)
    ev["incidents"] = incs
    ev["homeTeamScore"], ev["awayTeamScore"] = str(goals[0]), str(goals[1])
    ev.setdefault("scores", {})["matchStatusDetails"] = {"isNotStarted": False, "isInProgress": True, "isFinished": False,
                                                         "status": "inProgress", "liveTime": f"{minute}'"}
    return ev


def jsonify(o):
    return "application/json; charset=utf-8", json.dumps(o, ensure_ascii=False).encode("utf-8")


ROUTES, _tl = {}, threading.local()


def route(path):
    def deco(fn):
        ROUTES[path] = fn
        return fn
    return deco


def arg(k, default=None):
    return _tl.args.get(k, default)


def live_count():
    n = 0
    for d in (today(), (datetime.now(CAIRO) - timedelta(days=1)).strftime("%Y%m%d")):
        try:
            n += sum(1 for m in merged_day(d) if m["status"] in ("LIVE", "HT"))
        except Exception:  # noqa: BLE001
            pass
    return n


def decorate(ms):
    pending = 0
    for m in ms:
        PATHS[m["eid"]] = m
        m["pre"] = PREDS.get(m["eid"]) and PREDS[m["eid"]]["x1x2"]
        lp = LIVEP.get(m["eid"])
        m["livep"] = lp and lp["x1x2"]
        m["pick"] = pick_of(m) if m["status"] in ("NS", "LIVE", "HT") else None
        if m["status"] in ("NS", "LIVE", "HT") and m["eid"] not in PREDS:
            pending += 1
    return pending


@route("/api/cfg")
def api_cfg():
    return jsonify({"img": src.image_bases(), "standings": STANDINGS})


@route("/api/day")
def api_day():
    date = arg("date") or today()
    WATCH[date] = time.time()
    WAKE.set()
    ms = merged_day(date)
    ms.sort(key=lambda m: (league_key(m), m["kickoff"] or 0))
    pending = decorate(ms)
    return jsonify({"date": date, "pending": pending, "live_count": sum(1 for m in ms if m["status"] in ("LIVE", "HT")),
                    "matches": ms})


@route("/api/live")
def api_live():
    ms = []
    for d in (today(), (datetime.now(CAIRO) - timedelta(days=1)).strftime("%Y%m%d")):
        WATCH[d] = time.time()
        ms += [m for m in merged_day(d) if m["status"] in ("LIVE", "HT")]
    WAKE.set()
    seen, out = set(), []
    for m in sorted(ms, key=lambda m: (league_key(m), m["kickoff"] or 0)):
        if m["eid"] not in seen:
            seen.add(m["eid"])
            out.append(m)
    pending = decorate(out)
    return jsonify({"pending": pending, "live_count": len(out), "matches": out})


@route("/api/match")
def api_match():
    path = arg("path").strip("/")
    country, comp, slug, eid = path.split("/")
    OPEN[eid] = time.time()
    ev = summary(path)
    if FIX and arg("sim"):
        ev = demo_sim(ev, int(arg("sim")))
    inc = parse_incidents(ev)
    st = live_state(ev, inc)
    status = status_of(st)
    known = PATHS.get(eid) or {}
    home_n = known.get("home_ar") or ev.get("homeTeamName")
    away_n = known.get("away_ar") or ev.get("awayTeamName")
    ht = None
    for p in (ev.get("scores") or {}).get("scoresByPeriod", []):
        if "halfTime" in p.get("label", "") and p.get("home", {}).get("score") not in (None, ""):
            ht = [p["home"]["score"], p["away"]["score"]]
    c = COMP_AR.get(str(ev.get("competitionId")))
    resp = {"eid": eid, "path": path, "status": status, "live_time": st["live_time"],
            "home": home_n, "away": away_n, "home_en": ev.get("homeTeamName"), "away_en": ev.get("awayTeamName"),
            "home_badge": ev.get("homeTeamBadge"), "away_badge": ev.get("awayTeamBadge"),
            "home_color": ev.get("homeTeamFirstColor"), "away_color": ev.get("awayTeamFirstColor"),
            "league": (c[0] if c else None) or ev.get("competitionName"), "stage": ev.get("stageName"),
            "kickoff": ev.get("startDateTimeString"), "score": list(st["score"]) if st["started"] else None,
            "ht": ht, "incidents": inc}

    def t_stats():
        v = src.event_page(path, "stats", ttl=(lambda x: 3600 if st["finished"] else 20))
        return v["pageProps"]["initialEventData"]["event"].get("statistics")

    def t_lineups():
        out = {}
        for t in src.lineups(eid).get("Lu", []):
            side, starters, subs, coach = ("home" if t.get("Tnb") == 1 else "away"), [], [], None
            for p in t.get("Ps", []):
                name = (p.get("Snm") or f"{p.get('Fn', '')} {p.get('Ln', '')}").strip()
                rec = {"name": name, "num": p.get("Snu")}
                if p.get("Pon") == "COACH":
                    coach = name
                elif p.get("Fp"):
                    starters.append(rec)
                else:
                    subs.append(rec)
            out[side] = {"formation": "-".join(str(x) for x in t.get("Fo", [])), "starters": starters, "subs": subs, "coach": coach}
        return out

    def t_form():
        h = src.event_page(path, "h2h", ttl=1800)["pageProps"]["initialEventData"]["event"]["headToHead"]
        return {"home": simple_form(h.get("home")), "away": simple_form(h.get("away")), "h2h": simple_form(h.get("h2h"), 8)}

    jobs = {"lineups": EX.submit(t_lineups), "table": EX.submit(lambda: table_rows(src.table(country, comp))),
            "form": EX.submit(t_form)}
    if st["started"]:
        jobs["stats"] = EX.submit(t_stats)
    for k, f in jobs.items():
        try:
            v = f.result(timeout=25)
            if v:
                resp[k] = v
        except Exception as e:  # noqa: BLE001
            log(k, repr(e)[:100])

    if status in ("NS", "LIVE", "HT"):
        pre = PREDS.get(eid)
        if not pre:
            get_pre_bg({"eid": eid, "path": path, "country": country, "comp": comp, "status": status})
            resp["pred_state"] = "failed" if time.time() - PRED_ERR.get(eid, 0) < 120 else "pending"
        else:
            resp["pred"] = {k: v for k, v in pre.items() if k not in ("lh1", "la1", "lh2", "la2")}
            pk = best_picks(home_n, away_n, pre["x1x2"], pre["btts"], pre["over"])
            resp["pick_pre"] = {"best": pk[0] if pk else None, "alt": pk[1] if len(pk) > 1 else None}
            if status != "NS":
                try:
                    resp["live"] = live_probs(pre, st, fh_count(inc))
                    if resp["live"]:
                        lk = best_picks(home_n, away_n, resp["live"]["x1x2"], resp["live"]["btts"], resp["live"]["over"])
                        resp["pick_live"] = {"best": lk[0] if lk else None, "alt": lk[1] if len(lk) > 1 else None}
                except Exception as e:  # noqa: BLE001
                    log("live", repr(e)[:100])
    resp["hist"] = LIVEH.get(eid)
    return jsonify(resp)


@route("/api/track")
def api_track():
    rs = sorted((r for r in TRACK.values() if r["res"] and "s" in r["res"]), key=lambda r: -r["kick"])
    n = len(rs)
    pk = [r for r in rs if r["res"]["pk"] is not None]
    hi = [r for r in pk if r["pick"]["p"] >= 0.6]
    f = lambda a, b: round(100 * a / b) if b else None  # noqa: E731
    return jsonify({"n": n, "pending": sum(1 for r in TRACK.values() if r["res"] is None),
                    "acc": f(sum(r["res"]["ok1"] for r in rs), n), "brier": round(sum(r["res"]["brier"] for r in rs) / n, 3) if n else None,
                    "picks": len(pk), "pick_hit": f(sum(r["res"]["pk"] for r in pk), len(pk)),
                    "pick_exp": f(sum(r["pick"]["p"] for r in pk), len(pk)), "hi_n": len(hi), "hi_hit": f(sum(r["res"]["pk"] for r in hi), len(hi)),
                    "recent": [{"home": r["home"], "away": r["away"], "league": r["league"], "s": r["res"]["s"], "x": r["x"], "ok1": r["res"]["ok1"],
                                "pick": r["pick"] and r["pick"]["label"], "pk": r["res"]["pk"]} for r in rs[:25]]})


@route("/api/watch")
def api_watch():
    out = []
    for path in (arg("ids") or "").split(",")[:15]:
        try:
            path = path.strip("/")
            eid = path.split("/")[-1]
            ev = summary(path)
            inc = parse_incidents(ev)
            st = live_state(ev, inc)
            k = PATHS.get(eid) or {}
            gl = [i for i in inc if i["kind"] in ("goal", "pen_goal", "own_goal")]
            out.append({"eid": eid, "status": status_of(st), "score": list(st["score"]), "min": st["live_time"], "reds": sum(st["reds"]),
                        "home": k.get("home_ar") or ev.get("homeTeamName"), "away": k.get("away_ar") or ev.get("awayTeamName"),
                        "last": gl[-1] if gl else None})
        except Exception as e:  # noqa: BLE001
            log("watch", repr(e)[:80])
    return jsonify({"matches": out})


@route("/api/table")
def api_table():
    return jsonify({"rows": table_rows(src.table(arg("country"), arg("comp")))})


def nb_over(mean, line, disp=1.3):
    k = math.floor(line)
    if k < 0:
        return 1.0
    if mean <= 0:
        return 0.0
    r = mean / (disp - 1)
    p = r / (r + mean)
    pm, cdf = p ** r, 0.0
    for i in range(k + 1):
        cdf += pm
        pm *= (i + r) / (i + 1) * (1 - p)
    return max(0.0, min(1.0, 1 - cdf))


def po_over(mean, line):
    k = math.floor(line)
    return 1.0 if k < 0 else max(0.0, 1 - sum(pmf(i, mean) for i in range(k + 1)))


def obs(stats):
    def g(k):
        v = (stats or {}).get(k) or [0, 0]
        try:
            return [int(float(v[0] or 0)), int(float(v[1] or 0))]
        except Exception:  # noqa: BLE001
            return [0, 0]
    sot, off, blk = g("shotsOnTarget"), g("shotsOffTarget"), g("shotsBlocked")
    return {"corners": g("corners"), "cards": g("yellowCards"), "sot": sot, "shots": [sot[0] + off[0] + blk[0], sot[1] + off[1] + blk[1]]}


def deep(pre, st, stats, inc, home, away):
    lh, la = pre["lh2"], pre["la2"]
    tot, x = lh + la, pre["x1x2"]
    live = st["started"] and not st["finished"]
    pos = st["pos"] if live and st["pos"] is not None else 0.0
    f = remaining_fraction(pos)
    e = 1 - f
    sh, sa = st["score"] if live else (0, 0)
    fhn = fh_count(inc) if live else 0
    secs = []

    def sec(k, t, tier, note):
        s = {"k": k, "t": t, "tier": tier, "note": note, "items": []}
        secs.append(s)
        return s
    add = lambda s, lab, p: s["items"].append([lab, round(max(0.0, min(1.0, p)), 4)])  # noqa: E731
    g = sec("goals", "الأهداف", "live" if live else "data", "من قوة هجوم ودفاع الفريقين ومعدل الأهداف" + (" مع النتيجة والدقيقة الحالية" if live else ""))
    for t in (1.5, 2.5, 3.5, 4.5):
        add(g, f"أكتر من {t} هدف في الماتش", po_over(tot * f, t - sh - sa))
    for t in (1.5, 2.5):
        add(g, f"أقل من {t} هدف في الماتش", 1 - po_over(tot * f, t - sh - sa))
    for nm_, lam, cur in ((home, lh, sh), (away, la, sa)):
        add(g, f"{nm_} يسجل هدف أو أكتر", po_over(lam * f, .5 - cur))
        add(g, f"{nm_} يسجل هدفين أو أكتر", po_over(lam * f, 1.5 - cur))
    s1 = s2 = None
    if not live or pos < END1:
        s1 = sec("fh", "الشوط الأول", g["tier"], g["note"])
        lam1 = tot * remaining_fraction(pos, END1)
        for t in (0.5, 1.5, 2.5):
            add(s1, f"أكتر من {t} هدف في الشوط الأول", po_over(lam1, t - fhn))
        add(s1, "الشوط الأول بدون أهداف", 1 - po_over(lam1, .5 - fhn))
    if not live or pos < END2:
        s2 = sec("sh", "الشوط التاني", g["tier"], g["note"])
        cur = sh + sa - fhn if pos >= END1 else 0
        lam2 = tot * remaining_fraction(max(pos, END1))
        for t in (0.5, 1.5, 2.5):
            add(s2, f"أكتر من {t} هدف في الشوط التاني", po_over(lam2, t - cur))
    if not live:
        pm = lambda l: [pmf(i, l) for i in range(9)]  # noqa: E731
        R = range(9)

        def res(w):
            a, b = pm(lh * w), pm(la * w)
            return sum(a[i] * b[j] for i in R for j in R if i > j), sum(a[i] * b[i] for i in R), sum(a[i] * b[j] for i in R for j in R if i < j)
        for s, w, nmh in ((s1, .42, "الأول"), (s2, .58, "التاني")):
            r = res(w)
            add(s, f"فوز {home} في الشوط {nmh}", r[0])
            add(s, f"تعادل الشوط {nmh}", r[1])
            add(s, f"فوز {away} في الشوط {nmh}", r[2])
        p1, p2 = pm(tot * .42), pm(tot * .58)
        add(s2, "الشوط التاني أكتر تسجيلاً من الأول", sum(p1[i] * p2[j] for i in R for j in R if j > i))
        add(s1, "الشوط الأول أكتر تسجيلاً من التاني", sum(p1[i] * p2[j] for i in R for j in R if i > j))
        sm = score_matrix(pre["lh1"], pre["la1"])
        n, d = len(sm), sec("res", "النتيجة وفروق الأهداف", "data", "من مصفوفة النتايج الكاملة للمحرك")
        S = lambda c: sum(sm[i][j] for i in range(n) for j in range(n) if c(i, j))  # noqa: E731
        add(d, f"{home} شباكه نضيف", S(lambda i, j: j == 0))
        add(d, f"{away} شباكه نضيف", S(lambda i, j: i == 0))
        add(d, f"{home} يفوز من غير ما يتسجل عليه", S(lambda i, j: j == 0 and i > 0))
        add(d, f"{away} يفوز من غير ما يتسجل عليه", S(lambda i, j: i == 0 and j > 0))
        add(d, f"{home} يفوز بفارق هدفين أو أكتر", S(lambda i, j: i - j >= 2))
        add(d, f"{away} يفوز بفارق هدفين أو أكتر", S(lambda i, j: j - i >= 2))
        add(d, "إجمالي الأهداف 0-1", S(lambda i, j: i + j <= 1))
        add(d, "إجمالي الأهداف 2-3", S(lambda i, j: 2 <= i + j <= 3))
        add(d, "إجمالي الأهداف 4 أو أكتر", S(lambda i, j: i + j >= 4))
    k, c, sd = min(max(tot / 2.6, .8), 1.25), 1 - abs(x["H"] - x["A"]), lh / tot
    o = obs(stats) if live and stats else None
    wt = min(e * 1.2, .7) if (o and e > .08) else 0.0
    tier = "live" if wt else "est"
    note = "متوسط عام متعدّل بإحصائيات الماتش لحد دلوقتي" if wt else "تقدير بمتوسطات عامة معدّلة بقوة الفريقين، مش بيانات فعلية للماتشات اللي فاتت"
    for key, title, T, s, unit, lines, hl, tl in (
            ("corners", "الركنيات", 10 * k ** .5, .5 + .55 * (sd - .5) + .03, "ركنية", (8.5, 9.5, 10.5, 11.5), (3.5, 4.5), (3.5, 4.5, 5.5)),
            ("cards", "الكروت الصفراء", 3.7 + .8 * c, .5 - .25 * (sd - .5), "كارت أصفر", (2.5, 3.5, 4.5), (1.5, 2.5), (0.5, 1.5, 2.5)),
            ("sot", "التسديدات على المرمى", 8.6 * k ** .8, .5 + .7 * (sd - .5) + .03, "تسديدة على المرمى", (7.5, 8.5, 9.5), (3.5, 4.5), (3.5, 4.5)),
            ("shots", "التسديدات", 25 * k ** .6, .5 + .7 * (sd - .5) + .03, "تسديدة", (22.5, 24.5, 26.5), (10.5, 11.5), (10.5, 12.5))):
        nh, na = o[key] if wt else (0, 0)
        nt = nh + na
        rate = (1 - wt) * T + wt * (nt / max(e, .05))
        sl = (1 - wt) * s + wt * (nh / nt if nt else s)
        q, rem = sec(key, title, tier, note), rate * f
        for t in lines:
            add(q, f"أكتر من {t} {unit} في الماتش", nb_over(rem, t - nt))
        for t in tl:
            add(q, f"{home} أكتر من {t} {unit}", nb_over(rem * sl, t - nh))
            add(q, f"{away} أكتر من {t} {unit}", nb_over(rem * (1 - sl), t - na))
        if not live or pos < END1:
            for t in hl:
                add(q, f"أكتر من {t} {unit} في الشوط الأول", nb_over(rate * remaining_fraction(pos, END1), t - nt))
        if not live:
            for t in hl:
                add(q, f"أكتر من {t} {unit} في الشوط التاني", nb_over(rate * remaining_fraction(END1), t))
    r = sec("red", "الكارت الأحمر وركلات الجزاء", "est", "نسب تاريخية عامة")
    add(r, "كارت أحمر في الماتش", 1.0 if sum(st["reds"]) else 1 - math.exp(-.11 * f))
    add(r, "ركلة جزاء في الماتش", 1 - math.exp(-.28 * f))
    top = sorted(((p * (.92 if s["tier"] == "est" else 1.0), s["t"], lab, p) for s in secs for lab, p in s["items"] if .55 <= p <= .9 and 1 / p >= 1.12), reverse=True)
    cnt, out = {}, []
    for _, t, lab, p in top:
        if cnt.get(t, 0) < 3:
            cnt[t] = cnt.get(t, 0) + 1
            out.append({"label": lab, "p": round(p, 4), "odds": round(1 / p, 2), "sec": t})
    return {"state": "ok", "live": live, "min": st["live_time"], "top": out[:10], "secs": secs}


@route("/api/deep")
def api_deep():
    path = arg("path").strip("/")
    country, comp, slug, eid = path.split("/")
    pre = PREDS.get(eid) or get_pre(path, country, comp)
    if not pre:
        return jsonify({"state": "pending"})
    ev = summary(path)
    inc = parse_incidents(ev)
    st = live_state(ev, inc)
    stats = None
    if st["started"] and not st["finished"]:
        try:
            stats = src.event_page(path, "stats", ttl=3)["pageProps"]["initialEventData"]["event"].get("statistics")
        except Exception:  # noqa: BLE001
            stats = None
    k = PATHS.get(eid) or {}
    return jsonify(deep(pre, st, stats, inc, k.get("home_ar") or ev.get("homeTeamName"), k.get("away_ar") or ev.get("awayTeamName")))


@route("/api/health")
def api_health():
    return jsonify({"preds": len(PREDS), "live": len(LIVEP), "watching": list(WATCH), "source": src.info,
                    "day_mode": src.day_mode, "arabic_names": len(TEAM_AR)})



MANIFEST = {"name": "كورة لايف", "short_name": "كورة لايف", "start_url": "/", "scope": "/", "display": "standalone", "orientation": "portrait",
            "dir": "rtl", "lang": "ar", "background_color": "#0f1317", "theme_color": "#0f1317",
            "icons": [{"src": "/icon-192.png", "sizes": "192x192", "type": "image/png", "purpose": "any maskable"},
                      {"src": "/icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "any maskable"}],
            "shortcuts": [{"name": "الماتشات الشغالة", "url": "/#/"}, {"name": "أفضل الاختيارات", "url": "/#/picks"}]}
SW_JS = r"""const V='kl5';
self.addEventListener('install',e=>{self.skipWaiting();e.waitUntil(caches.open(V).then(c=>c.addAll(['/'])))});
self.addEventListener('activate',e=>e.waitUntil(caches.keys().then(k=>Promise.all(k.filter(x=>x!==V).map(x=>caches.delete(x)))).then(()=>clients.claim())));
self.addEventListener('fetch',e=>{const r=e.request,u=new URL(r.url);if(r.method!=='GET'||u.pathname.startsWith('/api/'))return;
e.respondWith(fetch(r).then(x=>{if(x.ok&&(u.origin===location.origin||/gstatic|googleapis/.test(u.host))){const c=x.clone();caches.open(V).then(k=>k.put(r,c))}return x}).catch(()=>caches.match(r).then(x=>x||caches.match('/'))))});
self.addEventListener('notificationclick',e=>{e.notification.close();const u=(e.notification.data||{}).url||'/';e.waitUntil(clients.matchAll({type:'window',includeUncontrolled:true}).then(l=>{for(const c of l){if('focus' in c){c.navigate('/'+u);return c.focus()}}return clients.openWindow('/'+u)}))});
self.addEventListener('push',e=>{let d={};try{d=e.data.json()}catch(x){}e.waitUntil(self.registration.showNotification(d.title||'كورة لايف',{body:d.body||'',icon:'/icon-192.png',data:{url:d.url||'#/'}}))});
"""
ICONS = {}


def _png(S):
    import struct
    import zlib
    rows, c = bytearray(), S / 2
    for y in range(S):
        rows.append(0)
        for x in range(S):
            t = (x + y) / (2 * S)
            r, g, b = 70 + (28 - 70) * t, 190 + (120 - 190) * t, 115 + (70 - 115) * t
            d = math.hypot(x + .5 - c, y + .5 - c) / S
            a = max(0.0, min(1.0, (0.04 - abs(d - 0.27)) * S / 1.4 + .5))
            q = max(0.0, min(1.0, (0.075 - d) * S / 1.4 + .5))
            r, g, b = r + (255 - r) * a, g + (255 - g) * a, b + (255 - b) * a
            r, g, b = r + (6 - r) * q, g + (21 - g) * q, b + (14 - b) * q
            rows += bytes((int(r), int(g), int(b)))
    ch = lambda k, d: struct.pack(">I", len(d)) + k + d + struct.pack(">I", zlib.crc32(k + d) & 0xffffffff)  # noqa: E731
    return b"\x89PNG\r\n\x1a\n" + ch(b"IHDR", struct.pack(">IIBBBBB", S, S, 8, 2, 0, 0, 0)) + ch(b"IDAT", zlib.compress(bytes(rows), 6)) + ch(b"IEND", b"")


def _icon(S):
    if S not in ICONS:
        ICONS[S] = _png(S)
    return "image/png", ICONS[S]


route("/icon-192.png")(lambda: _icon(192))
route("/favicon.ico")(lambda: _icon(192))
route("/icon-512.png")(lambda: _icon(512))
route("/apple-touch-icon.png")(lambda: _icon(180))
route("/manifest.webmanifest")(lambda: ("application/manifest+json; charset=utf-8", json.dumps(MANIFEST, ensure_ascii=False).encode("utf-8")))
route("/sw.js")(lambda: ("application/javascript; charset=utf-8", SW_JS.encode("utf-8")))


INDEX_HTML = r'''<!doctype html>
<html lang="ar" dir="rtl">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#0f1317"><link rel="manifest" href="/manifest.webmanifest"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="icon" href="/icon-192.png"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-status-bar-style" content="black-translucent"><meta name="apple-mobile-web-app-title" content="كورة لايف">
<title>كورة لايف</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Saira+Condensed:wght@500;600;700&family=Cairo:wght@600;700;800&family=IBM+Plex+Sans+Arabic:wght@300;400;500;600;700&display=swap" rel="stylesheet">
<style>
:root{
  --bg:#09090b; --card:#131316; --card2:#1b1b20; --line:#25252b; --ink:#f3f3f5; --mut:#9b9ba6; --dim:#62626c;
  --n:"Barlow Condensed","Readex Pro",system-ui,sans-serif; --red:#f0343a; --red-d:#3a1417; --away:#e6e6ec; --draw:#7b7b86; --ok:#35d08a;
}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
html,body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.6 "Readex Pro",system-ui,-apple-system,"Segoe UI",Tahoma,sans-serif;font-variant-numeric:tabular-nums;letter-spacing:-.1px}
body{padding-bottom:86px}
button,input{font:inherit;color:inherit}
svg{display:block}
.wrap{max-width:720px;margin:0 auto}
.ltr{direction:ltr;unicode-bidi:isolate}
/* ===== الشريط العلوي ===== */
header.top{position:sticky;top:0;z-index:30;background:rgba(9,9,11,.94);backdrop-filter:blur(10px)}
.bar{display:flex;align-items:center;gap:0;height:58px;padding:0 8px 0 4px}
.brand{display:flex;align-items:center;gap:8px;font-weight:700;font-size:17px;white-space:nowrap;margin-inline-end:auto;padding-inline-start:6px}
.mark{width:26px;height:26px;border-radius:7px;background:var(--red);display:grid;place-items:center}
.ib{width:36px;height:36px;display:grid;place-items:center;border:0;background:none;border-radius:50%;cursor:pointer;color:var(--ink);position:relative}
.ib:active{background:var(--card2)}
.ib svg{width:21px;height:21px}
.ib.dim{color:var(--mut)}
.ib input{position:absolute;inset:0;opacity:0;width:100%;cursor:pointer}
.livep{display:flex;align-items:center;gap:6px;height:30px;padding:0 11px;border-radius:99px;background:var(--card2);border:0;cursor:pointer;font-size:12.5px;font-weight:600;margin-inline-end:2px}
.livep i{width:7px;height:7px;border-radius:50%;background:var(--dim)}
.livep.has i{background:var(--red);animation:blink 1.4s steps(2,jump-none) infinite}
.livep.on{background:var(--red);color:#fff}.livep.on i{background:#fff}
@keyframes blink{50%{opacity:.25}}
.srow{display:none;padding:0 14px 10px}
.srow input{width:100%;background:var(--card);border:1px solid var(--line);border-radius:12px;padding:11px 14px;outline:none;font-size:14.5px}
.srow input:focus{border-color:var(--dim)}
.dline{padding:8px 16px 4px;color:var(--mut);font-weight:600;font-size:15px}
/* ===== التنقل السفلي ===== */
nav.bot{position:fixed;bottom:0;inset-inline:0;z-index:40;background:rgba(14,14,17,.97);backdrop-filter:blur(12px);border-top:1px solid var(--line);display:flex;padding-bottom:env(safe-area-inset-bottom)}
nav.bot a{flex:1;display:flex;flex-direction:column;align-items:center;gap:3px;padding:10px 4px 9px;color:var(--dim);font-size:12px;cursor:pointer;font-weight:500}
nav.bot a svg{width:24px;height:24px}
nav.bot a.on{color:var(--red)}
/* ===== الدوري والماتش ===== */
.lhd{display:flex;align-items:center;gap:11px;margin:14px 12px 8px;padding:11px 14px;background:var(--card);border-radius:14px;cursor:pointer}
.lhd .nm{font-weight:600;font-size:14.5px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.lhd .ct{color:var(--mut);font-size:12.5px;white-space:nowrap}
.lhd .ch{margin-inline-start:auto;color:var(--dim);transition:transform .2s}
.lhd.shut .ch{transform:rotate(90deg)}
.mc{margin:0 12px 8px;padding:15px 12px 13px;background:var(--card);border-radius:14px;cursor:pointer;position:relative;overflow:hidden;transition:background .15s}
.mc:active{background:var(--card2)}
.mc.lv::after{content:"";position:absolute;inset-inline-start:0;top:0;bottom:0;width:3px;background:var(--red)}
.mr{display:grid;grid-template-columns:1fr auto 1fr;align-items:center;gap:8px}
.tm{display:flex;align-items:center;gap:10px;min-width:0}
.tm.a{justify-content:flex-end}
.tm span.n{font-size:14.5px;font-weight:600;line-height:1.35;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.tm.lose span.n{color:var(--mut);font-weight:500}
.pill{min-width:80px;text-align:center;background:var(--card2);border-radius:10px;padding:7px 10px;font-weight:700;font-size:15.5px;line-height:1.25}
.pill small{display:block;font-size:11px;font-weight:600;color:var(--dim)}
.pill .sc{display:flex;justify-content:center;gap:7px}
.mc.lv .pill{background:var(--red-d);color:#fff}
.mc.lv .pill small{color:#ff6a6f}
.mc.lv .pill small i{font-style:normal;animation:blink 1.4s steps(2,jump-none) infinite}
.ps{margin-top:13px}
.ps .b{display:flex;height:4px;border-radius:3px;overflow:hidden;gap:2px}
.ps .b i{display:block;height:100%}
.ps .t{display:grid;grid-template-columns:repeat(3,1fr);margin-top:6px;font-size:11.5px;color:var(--dim)}
.ps .t span:nth-child(2){text-align:center}.ps .t span:nth-child(3){text-align:end}
.ps .t b{color:var(--ink);font-weight:700}
.pc{display:inline-flex;direction:ltr;align-items:baseline;gap:1px}.pc u{text-decoration:none;font-size:.62em;opacity:.7}
.hint{margin:6px 16px 10px;font-size:12.5px;color:var(--mut);line-height:1.8}
.empty{padding:56px 24px;text-align:center;color:var(--mut);line-height:2}
.sk{height:96px;margin:0 12px 8px;border-radius:14px;background:linear-gradient(90deg,var(--card),var(--card2),var(--card)) 0 0/200% 100%;animation:sh 1.3s infinite}
@keyframes sh{to{background-position:-200% 0}}
/* ===== الشعارات ===== */
.lg{position:relative;display:inline-grid;place-items:center;border-radius:50%;flex:none;overflow:hidden;color:#fff;font-weight:700;text-transform:uppercase}
.lg img{position:absolute;inset:0;width:100%;height:100%;object-fit:contain;background:#fff;padding:12%;border-radius:50%}
.lg.sq,.lg.sq img{border-radius:6px}
/* ===== الاختيارات ===== */
.pk{margin:0 12px 8px;background:var(--card);border-radius:14px;padding:14px;cursor:pointer;display:grid;grid-template-columns:auto 1fr auto;gap:12px;align-items:center}
.pk:active{background:var(--card2)}
.pk .rk{width:26px;height:26px;border-radius:50%;background:var(--card2);color:var(--mut);font-weight:700;font-size:13px;display:grid;place-items:center}
.pk:nth-child(-n+4) .rk{background:var(--red);color:#fff}
.pk .mt .lgn{font-size:11.5px;color:var(--mut);margin-bottom:6px}
.pk .mt .tl{display:flex;align-items:center;gap:8px;margin-top:5px;font-size:14px;font-weight:600}
.pk .what{font-size:13px;font-weight:600;max-width:150px;text-align:center;line-height:1.4;margin-top:6px}
.pk .cell{display:flex;flex-direction:column;align-items:center;min-width:104px}
/* ===== صفحة الماتش ===== */
.hero{margin:6px 12px 0;padding:18px 12px 16px;background:var(--card);border-radius:18px}
.hero .lgn{text-align:center;font-size:12.5px;color:var(--mut);margin-bottom:14px}
.hero .main{display:grid;grid-template-columns:1fr auto 1fr;align-items:start;gap:6px}
.hero .tmx{display:flex;flex-direction:column;align-items:center;gap:10px;text-align:center;font-weight:600;font-size:14.5px;line-height:1.35}
.hero .mid{text-align:center;min-width:100px;padding-top:8px}
.hero .score{display:flex;justify-content:center;align-items:center;gap:12px;font-size:42px;font-weight:700;line-height:1}
.hero .score i{font-style:normal;color:var(--dim);font-size:28px}
.hero .st{font-size:13px;color:var(--mut);margin-top:10px}
.hero .st.live{color:var(--red);font-weight:700}
.hero .st.live i{font-style:normal;animation:blink 1.4s steps(2,jump-none) infinite}
.mtabs{display:flex;overflow-x:auto;scrollbar-width:none;gap:8px;padding:14px 12px 4px}
.mtabs::-webkit-scrollbar{display:none}
.mtabs a{flex:none;padding:8px 16px;border-radius:99px;background:var(--card);color:var(--mut);font-size:13.5px;font-weight:500;cursor:pointer}
.mtabs a.on{background:var(--ink);color:#09090b;font-weight:700}
.sec{margin:12px 12px 0;padding:16px 14px;background:var(--card);border-radius:16px}
.sec h3{margin:0 0 16px;font-size:13px;color:var(--mut);font-weight:600;display:flex;align-items:center;gap:8px}
.tag{font-size:11px;padding:2px 9px;border-radius:99px;background:var(--red);color:#fff;font-weight:700}
.rings{display:grid;grid-template-columns:repeat(3,1fr);gap:20px 6px;justify-items:center}
.rings.two{grid-template-columns:repeat(2,1fr)}
.rg{display:flex;flex-direction:column;align-items:center;gap:7px;text-align:center;min-width:0}
.rg .r{position:relative;width:var(--s,84px);height:var(--s,84px)}
.rg svg{width:100%;height:100%}
.rg .tk{fill:none;stroke:var(--card2);stroke-width:9}
.rg .pg{fill:none;stroke-width:9;stroke-linecap:round}
.fresh .rg .pg{animation:fill 1s cubic-bezier(.2,.8,.2,1)}
@keyframes fill{from{stroke-dasharray:0 264}}
.rg .v{position:absolute;inset:0;display:grid;place-items:center;font-weight:700;font-size:calc(var(--s,84px)*.27)}
.rg .lb{font-size:12.5px;font-weight:600;line-height:1.35;max-width:104px}
.rg .od{font-size:11.5px;color:var(--mut);direction:ltr}
.rg .od b{color:var(--ink);font-weight:700}
.best{display:grid;grid-template-columns:auto 1fr;gap:16px;align-items:center}
.best .lab{font-size:19px;font-weight:700;line-height:1.4}
.best .kv{display:flex;gap:18px;margin-top:10px;flex-wrap:wrap}
.best .kv div{line-height:1.3}.best .kv b{display:block;font-size:15px}.best .kv span{font-size:11px;color:var(--mut)}
.note{font-size:12.5px;color:var(--mut);line-height:1.9}
.wait{display:flex;align-items:center;gap:12px;color:var(--mut);font-size:13.5px}
.spin{width:18px;height:18px;border:2px solid var(--line);border-top-color:var(--red);border-radius:50%;animation:rot .8s linear infinite;flex:none}
@keyframes rot{to{transform:rotate(360deg)}}
.skc{display:grid;grid-template-columns:repeat(3,1fr);gap:16px;margin-top:18px;justify-items:center}
.skc i{width:84px;height:84px;border-radius:50%;background:linear-gradient(90deg,var(--card),var(--card2),var(--card)) 0 0/200% 100%;animation:sh 1.3s infinite}
.xg{display:flex;justify-content:space-around;text-align:center}
.xg b{font-size:30px;font-weight:700;display:block;line-height:1.15}
.xg span{font-size:12.5px;color:var(--mut)}
/* أحداث وإحصائيات وغيرها */
.ev{display:grid;grid-template-columns:1fr 50px 1fr;gap:6px;padding:10px 0;border-top:1px solid var(--line);font-size:14px;align-items:start}
.ev:first-of-type{border-top:0}
.ev .m{text-align:center;color:var(--mut);font-size:12px;padding-top:2px;direction:ltr}
.ev .l{text-align:start}.ev .r{text-align:end}
.ev small{display:block;color:var(--mut);font-size:12px}
.ev .who{display:inline-flex;align-items:center;gap:8px}
.ic{display:inline-block;flex:none}
.ic.g{width:12px;height:12px;border-radius:50%;border:2px solid #fff;background:radial-gradient(circle,#fff 28%,transparent 30%)}
.ic.y,.ic.r{width:9px;height:13px;border-radius:2px}
.ic.y{background:#f2c230}.ic.r{background:var(--red)}
.ic.x{width:12px;height:12px;border-radius:50%;border:2px solid var(--dim)}
.sep{text-align:center;font-size:11.5px;color:var(--dim);padding:9px 0;border-top:1px dashed var(--line)}
.stat{padding:10px 0}
.stat .h{display:flex;justify-content:space-between;font-weight:700;font-size:14px}
.stat .h span.lb{font-weight:500;color:var(--mut);font-size:12.5px}
.stat .h b{direction:ltr}
.stat .b{display:flex;gap:3px;height:4px;margin-top:7px}
.stat .b i{display:block;height:100%;border-radius:2px}
.lu{display:grid;grid-template-columns:1fr 1fr;gap:18px}
.lu h4{margin:0 0 6px;font-size:13px;display:flex;align-items:center;gap:8px}
.lu .p{display:flex;gap:10px;padding:7px 0;font-size:13.5px;border-top:1px solid var(--line);direction:ltr}
.lu .p b{width:22px;color:var(--mut);font-weight:600;text-align:center}
table.tb{width:100%;border-collapse:collapse;font-size:13px}
table.tb th{color:var(--dim);font-weight:500;text-align:center;padding:6px 3px;font-size:11.5px}
table.tb td{padding:10px 3px;text-align:center;border-top:1px solid var(--line)}
table.tb td.nm{text-align:start;white-space:nowrap;max-width:150px;overflow:hidden;text-overflow:ellipsis}
table.tb td.nm span{display:inline-flex;align-items:center;gap:9px}
table.tb tr.hl td{background:#f0343a1f;font-weight:600}
.fm{display:grid;grid-template-columns:58px 1fr;gap:4px 8px;font-size:13px;padding:9px 0;border-top:1px solid var(--line)}
.fm:first-of-type{border-top:0}
.fm .dt{color:var(--mut);direction:ltr;text-align:end}
.chips{display:flex;gap:8px;overflow-x:auto;scrollbar-width:none;padding:6px 12px 6px}
.chips::-webkit-scrollbar{display:none}
.chips a{flex:none;padding:8px 15px;border-radius:99px;background:var(--card);color:var(--mut);font-size:13.5px;cursor:pointer}
.chips a.on{background:var(--ink);color:#09090b;font-weight:700}
/* شاشة الفلتر */
.shade{position:fixed;inset:0;background:#000a;z-index:60;display:none}
.sheet{position:fixed;bottom:0;inset-inline:0;max-width:720px;margin:0 auto;background:var(--card);border-radius:20px 20px 0 0;z-index:61;max-height:72vh;overflow:auto;padding:8px 8px 22px;display:none}
.sheet .grab{width:42px;height:4px;border-radius:2px;background:var(--line);margin:6px auto 12px}
.sheet a{display:flex;align-items:center;gap:12px;padding:12px;border-radius:12px;cursor:pointer;font-size:14.5px}
.sheet a:active,.sheet a.on{background:var(--card2)}
.sheet a em{margin-inline-start:auto;font-style:normal;color:var(--mut);font-size:12.5px}
footer.disc{padding:22px 16px 6px;font-size:11.5px;color:var(--dim);line-height:1.9}

/* ===== الخط والأرقام (Barlow Condensed للأرقام زي لوحات النتايج) ===== */
.pill,.pc,.hero .score,.xg b,.rg .v,.rg .od,.stat .h b,.ev .m,.fm .dt,table.tb td,table.tb th,.pk .rk,.ps .t,.livep #livecnt,.best .kv b.nn{font-family:var(--n)}
.pill{font-size:19px;letter-spacing:.5px;font-weight:600}
.pill small{font-family:"Readex Pro",sans-serif;font-size:10.5px;letter-spacing:0}
.hero .score{font-size:56px;font-weight:600;letter-spacing:1px}
.hero .score i{font-size:34px}
.xg b{font-size:40px;font-weight:600}
.rg .v{font-size:calc(var(--s,84px)*.34);font-weight:600}
.rg .od{font-size:13px}
.ps .t{font-size:13px}
.pc u{font-family:"Readex Pro",sans-serif}
/* ===== لمسات الشكل ===== */
.mc,.pk,.sec,.lhd,.hero{border:1px solid #ffffff0d}
.mc:active,.pk:active,.lhd:active{transform:scale(.985)}
.mc,.pk,.lhd{transition:transform .12s,background .15s}
.sec h3{font-weight:600;color:var(--ink);opacity:.82}
.sec h3::before{content:"";width:3px;height:14px;border-radius:2px;background:var(--red);flex:none}
.rg .pg.hot{filter:drop-shadow(0 0 5px rgba(240,52,58,.55))}
nav.bot{inset-inline:12px;bottom:calc(10px + env(safe-area-inset-bottom));border:1px solid #ffffff14;border-radius:22px;padding:5px;background:rgba(18,18,22,.88);box-shadow:0 10px 30px #000a;max-width:520px;margin:0 auto}
nav.bot a{padding:8px 4px 7px;border-radius:17px;gap:2px;transition:background .15s,color .15s}
nav.bot a.on{background:#f0343a24;color:#ff6a6f}
body{padding-bottom:104px}
.brand b{color:var(--red);font-weight:700}
.mark{background:linear-gradient(135deg,#ff5a4f,#d3141b);box-shadow:0 4px 14px #f0343a55}
.top5{display:flex;gap:10px;overflow-x:auto;scrollbar-width:none;padding:4px 12px 8px;scroll-snap-type:x mandatory}
.top5::-webkit-scrollbar{display:none}
.tp{flex:0 0 218px;scroll-snap-align:start;background:linear-gradient(160deg,#2a1013,var(--card) 60%);border:1px solid #f0343a33;border-radius:16px;padding:14px;cursor:pointer;display:grid;grid-template-columns:1fr auto;gap:10px;align-items:center}
.tp .ml{font-size:12.5px;line-height:1.5;font-weight:600}
.tp .ml small{display:block;font-weight:400;color:var(--mut);font-size:11px;margin-bottom:4px}
.tp .wh{font-size:12px;color:#ff8a8e;margin-top:6px;font-weight:600;line-height:1.4}
.sh{padding:6px 16px 4px;font-size:12.5px;color:var(--mut);font-weight:600;display:flex;align-items:center;gap:8px}
.sh::before{content:"";width:3px;height:13px;border-radius:2px;background:var(--red)}

/* ===== v5: هوية جديدة (أخضر ملعب + خطوط Cairo / IBM Plex / Saira) ===== */
:root{--bg:#0f1317;--card:#0f141b;--card2:#171e29;--line:#212a38;--ink:#eef2f7;--mut:#93a0b4;--dim:#5d6a7c;--acc:#2ee59d;--live:#ff4d5a;--red:#2ee59d;--red-d:#12352a;--away:#e8edf5;--draw:#6c7889;
--n:"Saira Condensed","Cairo",system-ui,sans-serif;--f:"IBM Plex Sans Arabic","Cairo",system-ui,sans-serif;--h:"Cairo","IBM Plex Sans Arabic",sans-serif}
html,body{background:radial-gradient(130% 55% at 50% -8%,#0c2d24,transparent 62%) no-repeat,var(--bg);font-family:var(--f);letter-spacing:0}
.brand,.sec h3,.sh,.lhd .nm,.dline,.mtabs a,.chips a,nav.bot a,.tag,.hint{font-family:var(--h)}
header.top{background:rgba(6,8,12,.9);padding-top:env(safe-area-inset-top)}
.mark{background:linear-gradient(135deg,#7dffc4,#12b878);box-shadow:0 4px 16px #2ee59d44}.mark svg{stroke:#04150e}.brand b{color:var(--acc)}
.mc,.pk,.sec,.lhd,.hero{background:linear-gradient(180deg,#131a24,var(--card));border:1px solid #ffffff0f;border-radius:18px}
.lhd{border-inline-start:3px solid var(--lc,var(--acc));border-radius:14px}
.pill{background:#0b1017;border:1px solid var(--line)}.pill small,.pc u{font-family:var(--f)}
.livep.has i,.mc.lv::after{background:var(--live)}.livep.on{background:var(--live)}
.mc.lv .pill{background:#2a1218;border-color:#ff4d5a44}.mc.lv .pill small,.hero .st.live{color:var(--live)}.ic.r{background:var(--live)}
.tag,.pk:nth-child(-n+4) .rk{color:#04150e}
nav.bot a{font-size:11px}nav.bot a.on{background:#2ee59d1f;color:var(--acc)}
.tp{background:linear-gradient(160deg,#0d2b22,var(--card) 60%);border-color:#2ee59d33}.tp .wh{color:var(--acc)}
.rg .pg.hot{filter:drop-shadow(0 0 6px #2ee59d88)}table.tb tr.hl td{background:#2ee59d1c}
.mtabs a.on,.chips a.on{background:var(--acc);color:#04150e}
.bell{position:absolute;top:3px;inset-inline-end:5px;width:26px;height:26px;border:0;background:none;color:var(--dim);display:grid;place-items:center;border-radius:50%;cursor:pointer}.bell.on{color:var(--acc)}
.acts{display:flex;gap:8px;padding:10px 12px 0}
.btn,.act{border:0;border-radius:99px;background:var(--acc);color:#04150e;font:600 13px var(--h);padding:8px 16px;cursor:pointer}
.act{background:var(--card2);color:var(--ink);display:flex;align-items:center;gap:6px}.act.on{background:#2ee59d26;color:var(--acc)}.btn.g{background:var(--card2);color:var(--mut)}
.toast{position:fixed;top:calc(12px + env(safe-area-inset-top));inset-inline:12px;max-width:520px;margin:0 auto;z-index:90;background:#182230;border:1px solid #2ee59d44;border-radius:14px;padding:12px 14px;font-size:13.5px;box-shadow:0 10px 30px #000a;animation:tin .25s;cursor:pointer}
@keyframes tin{from{transform:translateY(-20px);opacity:0}}
.mrow{display:flex;align-items:center;gap:12px;padding:12px 10px;border-top:1px solid var(--line)}.mrow>div{flex:1;min-width:0}.mrow b{display:block;font-size:14.5px}.mrow small{color:var(--mut);font-size:12px;line-height:1.7}
.lgd{display:flex;justify-content:space-between;font-size:12px;margin-top:8px}
/* ===== v6: ألوان واقعية + خط أكبر ===== */
:root{--bg:#0f1317;--card:#171c22;--card2:#1e252c;--line:#2a323b;--ink:#f2f4f6;--mut:#a2abb5;--dim:#6d7782;--acc:#3dba6f;--live:#e5484d;--red:#3dba6f;--red-d:#2a1517;--away:#dfe4ea;--draw:#6f7a86}
html,body{background:var(--bg);font-size:16px}
.mark{background:var(--acc);box-shadow:none}
.mc,.pk,.sec,.lhd,.hero{background:var(--card);border:1px solid var(--line);border-radius:14px}
.tp{background:var(--card);border-color:var(--line)}
.rg .pg.hot{filter:none}.toast{box-shadow:none}
header.top{background:rgba(15,19,23,.96)}
nav.bot{background:rgba(23,28,34,.97);box-shadow:none;border-color:var(--line)}nav.bot a{font-size:12.5px}nav.bot a.on{background:#3dba6f22}
.tm span.n{font-size:16px}.pill{font-size:21px}.pill small{font-size:12px}
.lhd .nm{font-size:16px}.lhd .ct{font-size:13.5px}.dline{font-size:16px}
.sec h3{font-size:15px}.rg .lb{font-size:14px;max-width:116px}.rg .od{font-size:14px}.note,.hint{font-size:14px}
.ps .t{font-size:14px}.mtabs a,.chips a{font-size:15px}.pk .mt .tl{font-size:16px}.pk .what{font-size:14px}.pk .mt .lgn{font-size:13px}
.ev,.fm,.lu .p,table.tb{font-size:14.5px}.stat .h{font-size:15px}.hero .tmx{font-size:16px}.tp .ml{font-size:14px}.tp .wh{font-size:13px}
.lg img{background:none;padding:0;border-radius:0}.lg.ok{background:none!important;color:transparent;overflow:visible;border-radius:0}
.dstrip{display:flex;gap:6px;overflow-x:auto;scrollbar-width:none;direction:ltr;position:relative;padding:8px 12px 4px}.dstrip::-webkit-scrollbar{display:none}
.dchip{flex:none;width:56px;padding:7px 0;border-radius:12px;background:var(--card);border:1px solid var(--line);text-align:center;cursor:pointer;color:var(--mut)}
.dchip small{display:block;font-size:12.5px;font-family:var(--h)}.dchip b{font:600 20px var(--n);color:var(--ink)}.dchip.on{background:var(--acc);border-color:var(--acc);color:#07170d}.dchip.on b{color:#07170d}
#dprev,#dnext{display:none!important}
.fd{display:flex;gap:4px;justify-content:center}.fd i{width:9px;height:9px;border-radius:50%;background:var(--dim)}.fd .w{background:var(--acc)}.fd .l{background:var(--live)}
.dr{display:grid;grid-template-columns:1fr auto;gap:4px 10px;align-items:center;padding:10px 0;border-top:1px solid var(--line);font-size:15px}.dr:first-of-type{border-top:0}.dr small{display:block;color:var(--mut);font-size:12.5px}.dr>b{font:600 19px var(--n)}.dr .b{grid-column:1/-1;height:4px;border-radius:2px;background:var(--card2)}.dr .b i{display:block;height:100%;border-radius:2px;background:var(--acc)}.tag.est{background:#c9972b}.tag.live{background:var(--live);color:#fff}
details.mored>summary{margin:12px 12px 0;padding:13px;border-radius:12px;background:var(--card2);text-align:center;font:600 14.5px var(--h);cursor:pointer;list-style:none}details.mored>summary::-webkit-details-marker{display:none}
.pfc{padding-top:0}
</style>
</head>
<body>
<div class="wrap">
<header class="top" id="top">
  <div class="bar" id="bar">
    <div class="brand"><span class="mark"><svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="#fff" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="9"/><path d="M12 7l4 3-1.5 5h-5L8 10z"/></svg></span>كورة<b>لايف</b></div>
    <button class="livep" id="livep"><i></i><span>لايف</span><span id="livecnt"></span></button>
    <button class="ib" id="fbtn" aria-label="فلتر"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round" stroke-linejoin="round"><path d="M4 5h16l-6 8v6l-4-2v-4z"/></svg></button>
    <button class="ib" id="sbtn" aria-label="بحث"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round"><circle cx="11" cy="11" r="7"/><path d="M20 20l-3.5-3.5"/></svg></button>
    <button class="ib dim" id="dprev" aria-label="اليوم اللي قبله"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M9 6l6 6-6 6"/></svg></button>
    <label class="ib" aria-label="التاريخ"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round"><rect x="4" y="5" width="16" height="15" rx="3"/><path d="M4 10h16M9 3v4M15 3v4"/></svg><input type="date" id="dpick"></label>
    <button class="ib dim" id="dnext" aria-label="اليوم اللي بعده"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M15 6l-6 6 6 6"/></svg></button>
    <button class="ib" id="back" style="display:none" aria-label="رجوع"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round"><path d="M9 6l6 6-6 6"/></svg></button>
    <div id="mtitle" class="brand" style="display:none;font-size:16px"></div>
  </div>
  <div class="srow" id="srow"><input id="q" placeholder="ابحث عن فريق أو دوري"></div>
</header>
<main id="app"></main>
<footer class="disc">التوقعات احتمالات إحصائية مبنية على نتايج الفرق، مش ضمانات ولا نصايح مراهنة. «أفضل اختيار» معناه أعلى احتمال عند المحرك، مش إنه فيه قيمة قصاد odds شركات المراهنات. الـodds اللي في الموقع = ١ ÷ الاحتمال. البيانات من مصدر غير رسمي وممكن تتأخر أو تتغير.</footer>
</div>
<nav class="bot" id="nav">
  <a data-r=""><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><rect x="3" y="5" width="18" height="14" rx="2"/><path d="M12 5v14M3 12h4M17 12h4"/><circle cx="12" cy="12" r="2.5"/></svg>المباريات</a>
  <a data-r="picks"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="9"/><circle cx="12" cy="12" r="5"/><circle cx="12" cy="12" r="1.2"/></svg>الاختيارات</a>
  <a data-r="standings"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><rect x="4" y="12" width="4" height="8" rx="1"/><rect x="10" y="4" width="4" height="16" rx="1"/><rect x="16" y="9" width="4" height="11" rx="1"/></svg>الترتيب</a>
<a data-r="track"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M4 19V5M4 19h16M8 15l4-5 3 3 5-7"/></svg>السجل</a>
  <a data-r="more"><svg viewBox="0 0 24 24" fill="currentColor"><circle cx="5" cy="12" r="1.7"/><circle cx="12" cy="12" r="1.7"/><circle cx="19" cy="12" r="1.7"/></svg>المزيد</a>
</nav>
<svg width="0" height="0" style="position:absolute"><defs><linearGradient id="gR" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#4ccb7d"/><stop offset="1" stop-color="#34ab62"/></linearGradient><linearGradient id="gW" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#ffffff"/><stop offset="1" stop-color="#b4b4c0"/></linearGradient><linearGradient id="gD" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#9a9aa6"/><stop offset="1" stop-color="#666672"/></linearGradient></defs></svg>
<div class="shade" id="shade"></div><div class="sheet" id="sheet"></div>

<script>
const $ = s => document.querySelector(s);
const app = $('#app');
let timer = null, CFG = {img:{team:[],comp:[]}, standings:[]};
const state = {date:null, q:'', live:false, league:'all', collapsed:{}, liveN:0, std:null};
const CACHE = {};
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const P = x => Math.round(x * 100);
const pc = x => `<span class="pc"><b>${P(x)}</b><u>%</u></span>`;
const od = p => p > 0.005 ? (1 / p).toFixed(2) : '—';
const nm = (m, k) => m[k + '_ar'] || m[k];

/* ---------- الشعارات: بنجرّب عناوين، ولو فشلت بيفضل الحرف الأول بلون الفريق ---------- */
function hue(s){ let h = 0; for (const c of String(s||'')) h = (h*31 + c.charCodeAt(0)) % 360; return h; }
function initials(n){ const w = String(n||'?').replace(/[^A-Za-z؀-ۿ ]/g,'').trim().split(/\s+/); return ((w[0]||'?')[0] + (w[1]?w[1][0]:'')).slice(0,2); }
function logo(kind, img, name, size, color, sq){
  const bg = color && /^[0-9a-f]{6}$/i.test(color) ? '#' + color : `hsl(${hue(name)} 45% 34%)`;
  const bases = CFG.img[kind] || [];
  const im = img && bases.length ? `<img loading="lazy" alt="" data-k="${kind}" data-i="0" data-p="${esc(img)}" src="${bases[0]}${esc(img)}" onerror="imgErr(this)" onload="this.parentNode.classList.add('ok')">` : '';
  return `<span class="lg${sq?' sq':''}" style="width:${size}px;height:${size}px;font-size:${Math.round(size*.4)}px;background:${bg}">${esc(initials(name))}${im}</span>`;
}
function imgErr(el){ const b = CFG.img[el.dataset.k] || [], i = +el.dataset.i + 1; if (i < b.length){ el.dataset.i = i; el.src = b[i] + el.dataset.p; } else el.remove(); }

/* ---------- تواريخ ---------- */
const ymd = d => d.getFullYear() + String(d.getMonth()+1).padStart(2,'0') + String(d.getDate()).padStart(2,'0');
const parseYmd = s => new Date(+s.slice(0,4), +s.slice(4,6)-1, +s.slice(6,8));
function shiftDate(s, n){ const d = parseYmd(s); d.setDate(d.getDate()+n); return ymd(d); }
const hhmm = e => new Date(e*1000).toLocaleTimeString('en-GB',{hour:'2-digit',minute:'2-digit',hour12:false});
function dateLine(s){
  const t = ymd(new Date()), d = parseYmd(s);
  const w = s === t ? 'النهارده' : s === shiftDate(t,1) ? 'بكرة' : s === shiftDate(t,-1) ? 'امبارح' : d.toLocaleDateString('ar-EG-u-nu-latn',{weekday:'long'});
  return `${w}، ${d.toLocaleDateString('ar-EG-u-nu-latn',{day:'numeric',month:'long',year:'numeric'})}`;
}
function kickStr(s){
  if (!s) return '';
  const d = new Date(Date.UTC(+s.slice(0,4), +s.slice(4,6)-1, +s.slice(6,8), +s.slice(8,10), +s.slice(10,12)));
  return d.toLocaleDateString('ar-EG-u-nu-latn',{weekday:'long',day:'numeric',month:'long'}) + ' · ' + d.toLocaleTimeString('en-GB',{hour:'2-digit',minute:'2-digit',hour12:false});
}
async function api(url){ const r = await fetch(url); if(!r.ok) throw new Error(r.status); return r.json(); }
const clearTimer = () => { if (timer) clearTimeout(timer), timer = null; };

/* ---------- الهيدر والتنقل ---------- */
function chrome(r){
  const m = r === 'm', home = r === '';
  ['#livep','#fbtn','#sbtn','#dprev','#dnext'].forEach(s => $(s).style.display = home ? '' : 'none');
  $('#dpick').parentElement.style.display = home ? '' : 'none';
  $('#back').style.display = m ? 'grid' : 'none';
  $('#mtitle').style.display = m ? 'block' : 'none';
  document.querySelector('.bar .brand').style.display = m ? 'none' : '';
  if (!home) $('#srow').style.display = 'none';
  $('#nav').style.display = m ? 'none' : 'flex';
  document.querySelectorAll('#nav a').forEach(a => { a.classList.toggle('on', a.dataset.r === r); a.onclick = () => a.dataset.r === 'more' ? openMore() : (location.hash = '#/' + a.dataset.r); });
}
$('#back').onclick = () => { history.length > 1 ? history.back() : (location.hash = '#/'); };
$('#sbtn').onclick = () => { const r = $('#srow'); r.style.display = r.style.display === 'block' ? 'none' : 'block'; if (r.style.display === 'block') $('#q').focus(); };
$('#livep').onclick = () => { state.live = !state.live; viewList(); };
$('#dprev').onclick = () => { state.date = shiftDate(state.date || ymd(new Date()), -1); state.live = false; viewList(); };
$('#dnext').onclick = () => { state.date = shiftDate(state.date || ymd(new Date()), 1); state.live = false; viewList(); };
$('#dpick').onchange = e => { if (e.target.value){ state.date = e.target.value.replaceAll('-',''); state.live = false; viewList(); } };
function setLive(n){ state.liveN = n; const b = $('#livep'); $('#livecnt').textContent = n ? n : ''; b.classList.toggle('has', n > 0); b.classList.toggle('on', state.live); }

/* ---------- الحلقات (الدوائر) ---------- */
const R = 42, C = 2 * Math.PI * R;
function ring(p, o = {}){
  const s = o.size || 84, c0 = o.color || (p >= 0.5 ? 'var(--red)' : 'var(--draw)');
  const col = {'var(--red)':'url(#gR)','var(--away)':'url(#gW)','var(--draw)':'url(#gD)'}[c0] || c0, hot = col === 'url(#gR)' ? ' hot' : '';
  const d = Math.max(Math.min(p, 1), 0) * C;
  return `<div class="rg" style="--s:${s}px"><div class="r"><svg viewBox="0 0 100 100"><circle class="tk" cx="50" cy="50" r="${R}"/>
    ${d > 1 ? `<circle class="pg${hot}" cx="50" cy="50" r="${R}" transform="rotate(-90 50 50)" style="stroke:${col};stroke-dasharray:${d.toFixed(1)} ${C.toFixed(1)}"/>` : ''}</svg>
    <div class="v">${pc(p)}</div></div>${o.label ? `<div class="lb">${o.label}</div>` : ''}<div class="od">odds <b>${od(p)}</b></div></div>`;
}

/* ---------- قايمة الماتشات ---------- */
const groupBy = ms => { const g = []; for (const m of ms){ let x = g[g.length-1]; if (!x || x.key !== m.comp_id) { x = {key: m.comp_id, name: m.league_ar || m.league, country: m.country_ar || m.country_name, badge: m.league_badge, m: []}; g.push(x); } x.m.push(m); } return g; };
function applyFilters(ms){
  const q = $('#q').value.trim().toLowerCase();
  return ms.filter(m => (state.league === 'all' || m.comp_id === state.league) &&
    (!q || [m.home, m.away, m.home_ar, m.away_ar, m.league, m.league_ar, m.country_name].join(' ').toLowerCase().includes(q)));
}
const skeleton = (n = 6) => '<div class="sk"></div>'.repeat(n);

async function viewList(kind = ''){ // '' | 'picks'
  clearTimer(); chrome(kind);
  const t = ymd(new Date());
  if (!state.date) state.date = t;
  if (kind === 'picks') state.live = false;
  const url = kind === 'picks' ? '/api/day?date=' + t : (state.live ? '/api/live' : '/api/day?date=' + state.date);
  const ck = url;
  if (kind === '') $('#dpick').value = `${state.date.slice(0,4)}-${state.date.slice(4,6)}-${state.date.slice(6,8)}`;
  let last = null;
  const draw = data => {
    last = data; window._ms = window._ms || {}; data.matches.forEach(x => window._ms[x.eid] = x);
    setLive(data.live_count || 0);
    let list = data.matches;
    if (kind === 'picks') list = list.filter(m => m.pick && m.status !== 'FT');
    const all = list;
    list = applyFilters(list);
    let h = '';
    if (kind === 'picks'){
      h += '<div class="chips pfc">' + [['all','الكل'],['res','نتيجة الماتش'],['goals','أهداف'],['strong','قوية فقط']].map(([k,l]) => `<a data-pf="${k}" class="${state.pf===k?'on':''}">${l}</a>`).join('') + '</div>';
      h += '<div class="hint">أفضل اختيار لكل ماتش حسب المحرك، مرتب بالأعلى احتمال، وبيتحدث مع الماتش الشغال.</div>';
      list = list.filter(pfOk); list.sort((a, b) => b.pick.best.p - a.pick.best.p);
      list.slice(0, 60).forEach((m, i) => h += pickCard(m, i + 1));
      if (!list.length) h += `<div class="empty">${data.pending ? 'المحرك بيحسب توقعات ' + data.pending + ' ماتش دلوقتي، هتظهر هنا لوحدها.' : 'مفيش اختيارات واضحة دلوقتي.'}</div>`;
    } else {
      h += dayStrip() + `<div class="dline">${state.live ? 'الماتشات الشغالة دلوقتي' : esc(dateLine(state.date))}</div>`;
      const tops = (state.live || $('#q').value.trim() || state.league !== 'all') ? [] : data.matches.filter(m => m.pick && m.status !== 'FT').sort((a, b) => b.pick.best.p - a.pick.best.p).slice(0, 6);
      if (tops.length >= 2) h += `<div class="sh">أقوى اختيارات المحرك</div><div class="top5">${tops.map(topCard).join('')}</div>`;
      if (!list.length) h += `<div class="empty">${state.live ? 'مفيش ماتشات شغالة دلوقتي.' : 'مفيش ماتشات في اليوم ده.'}</div>`;
      for (const g of buildGroups(list)){
        const shut = state.collapsed[g.key];
        h += `<div class="lhd ${shut?'shut':''}" data-k="${esc(g.key)}" style="--lc:hsl(${hue(g.key)} 70% 58%)">${g.key==='fav'?STAR:g.key==='live'?LIVEDOT:logo('comp', g.badge, g.name, 26, null, true)}<span class="nm">${esc(g.name)}</span><span class="ct">${esc(g.country)}</span>
          <svg class="ch" width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round"><path d="M6 9l6 6 6-6"/></svg></div>`;
        if (!shut) for (const m of g.m) h += card(m);
      }
    }
    if (data.pending && kind === '' && list.length) h += `<div class="hint">المحرك بيحسب توقعات ${data.pending} ماتش، هتظهر لوحدها.</div>`;
    const y = scrollY; app.innerHTML = h; scrollTo(0, y);
    app.querySelectorAll('.lhd').forEach(x => x.onclick = () => { state.collapsed[x.dataset.k] = !state.collapsed[x.dataset.k]; draw(last); });
    app.querySelectorAll('[data-p]').forEach(r => r.onclick = () => { location.hash = '#/m/' + r.dataset.p; });
    app.querySelectorAll('[data-pf]').forEach(a => a.onclick = () => { state.pf = a.dataset.pf; draw(last); });
    app.querySelectorAll('[data-d]').forEach(a => a.onclick = () => { state.date = a.dataset.d; state.live = false; viewList(); });
    { const on = $('.dchip.on'), sp = $('#dstrip'); if (on && sp) sp.scrollLeft = on.offsetLeft - sp.clientWidth / 2 + on.offsetWidth / 2; }
    app.querySelectorAll('[data-b]').forEach(b => b.onclick = async e => { e.stopPropagation(); await toggleFollow(window._ms[b.dataset.b]); draw(last); });
    window._redraw = () => draw(last); window._leagues = all;
  };
  if (CACHE[ck]) draw(CACHE[ck]); else app.innerHTML = skeleton();
  const load = async () => {
    try {
      const d = await api(url); CACHE[ck] = d; draw(d);
      const anyLive = d.matches.some(m => m.status === 'LIVE' || m.status === 'HT');
      timer = setTimeout(load, anyLive ? 10000 : (d.pending ? 4000 : 40000));
    } catch(e){ if (!CACHE[ck]) app.innerHTML = '<div class="empty">مقدرتش أجيب الماتشات دلوقتي، بحاول تاني...</div>'; timer = setTimeout(load, 6000); }
  };
  await load();
}
$('#q').oninput = () => window._redraw && window._redraw();
$('#fbtn').onclick = () => {
  const by = new Map();
  for (const m of (window._leagues || [])){ const e = by.get(m.comp_id) || {name: m.league_ar || m.league, country: m.country_ar || m.country_name, badge: m.league_badge, n: 0}; e.n++; by.set(m.comp_id, e); }
  let h = '<div class="grab"></div>' + `<a class="${state.league==='all'?'on':''}" data-l="all"><span>كل الدوريات</span><em>${(window._leagues||[]).length}</em></a>`;
  for (const [k, e] of by) h += `<a class="${state.league===k?'on':''}" data-l="${esc(k)}">${logo('comp', e.badge, e.name, 28, null, true)}<span>${esc(e.name)} <span style="color:var(--mut);font-size:12px">· ${esc(e.country)}</span></span><em>${e.n}</em></a>`;
  $('#sheet').innerHTML = h; $('#sheet').style.display = $('#shade').style.display = 'block';
  $('#sheet').querySelectorAll('a').forEach(a => a.onclick = () => { state.league = a.dataset.l; closeSheet(); window._redraw && window._redraw(); });
};
const closeSheet = () => { $('#sheet').style.display = $('#shade').style.display = 'none'; };
$('#shade').onclick = closeSheet;

function card(m){
  const lv = m.status === 'LIVE' || m.status === 'HT', fin = m.status === 'FT';
  const hs = +m.hs, as = +m.as, started = !(m.status === 'NS' || m.status === 'OFF');
  let pill;
  if (!started) pill = `<div class="pill"><span class="ltr">${m.status === 'OFF' ? 'اتأجل' : (m.kickoff ? hhmm(m.kickoff) : '')}</span></div>`;
  else pill = `<div class="pill">${lv ? `<small><i>●</i> ${m.status === 'HT' ? 'استراحة' : esc(m.minute || '')}</small>` : ''}<div class="sc"><span>${m.hs ?? 0}</span><span style="color:var(--dim)">-</span><span>${m.as ?? 0}</span></div>${fin ? '<small>انتهى</small>' : ''}</div>`;
  const p = lv ? (m.livep || m.pre) : m.pre;
  let ps = '';
  if (!fin && m.status !== 'OFF' && p){
    const w = [p.H, p.D, p.A].map(x => Math.max(x * 100, 3)), mx = Math.max(p.H, p.D, p.A);
    const cell = (x, l) => `<span>${l} ${x === mx ? `<b>${pc(x)}</b>` : pc(x)}</span>`;
    ps = `<div class="ps"><div class="b"><i style="width:${w[0]}%;background:var(--red)"></i><i style="width:${w[1]}%;background:var(--draw)"></i><i style="width:${w[2]}%;background:var(--away)"></i></div>
      <div class="t">${cell(p.H,'1')}${cell(p.D,'X')}${cell(p.A,'2')}</div></div>`;
  }
  return `<div class="mc ${lv?'lv':''}" data-p="${esc(m.path)}">${bellBtn(m)}<div class="mr">
    <div class="tm ${fin && as > hs ? 'lose' : ''}"><span class="n">${esc(nm(m,'home'))}</span>${logo('team', m.home_img, nm(m,'home'), 34, m.home_color)}</div>${pill}
    <div class="tm a ${fin && hs > as ? 'lose' : ''}">${logo('team', m.away_img, nm(m,'away'), 34, m.away_color)}<span class="n">${esc(nm(m,'away'))}</span></div></div>${ps}</div>`;
}
function topCard(m){
  const b = m.pick.best;
  return `<div class="tp" data-p="${esc(m.path)}"><div class="ml"><small>${esc(m.league_ar || m.league)}</small>${esc(nm(m,'home'))}<br>${esc(nm(m,'away'))}<div class="wh">${esc(b.label)}</div></div>${ring(b.p, {size: 66})}</div>`;
}
function pickCard(m, i){
  const b = m.pick.best, lv = m.status === 'LIVE' || m.status === 'HT';
  const when = lv ? `لايف ${m.status === 'HT' ? '(استراحة)' : esc(m.minute || '')} · ${m.hs ?? 0}-${m.as ?? 0}` : (m.kickoff ? hhmm(m.kickoff) : '');
  return `<div class="pk" data-p="${esc(m.path)}"><div class="rk">${i}</div>
    <div class="mt"><div class="lgn">${esc(m.league_ar || m.league)} · ${when}</div>
      <div class="tl">${logo('team', m.home_img, nm(m,'home'), 22, m.home_color)}<span>${esc(nm(m,'home'))}</span></div>
      <div class="tl">${logo('team', m.away_img, nm(m,'away'), 22, m.away_color)}<span>${esc(nm(m,'away'))}</span></div></div>
    <div class="cell">${ring(b.p, {size: 74})}<div class="what">${esc(b.label)}</div></div></div>`;
}

/* ---------- الترتيب ---------- */
async function viewStandings(sel){
  clearTimer(); chrome('standings');
  const list = CFG.standings || [];
  const cur = sel || (list[0] && list[0][1]);
  let h = '<div class="chips">' + list.map(([n, p]) => `<a data-s="${esc(p)}" class="${p===cur?'on':''}">${esc(n)}</a>`).join('') + '</div><div id="stb">' + skeleton(3) + '</div>';
  app.innerHTML = h;
  app.querySelectorAll('.chips a').forEach(a => a.onclick = () => viewStandings(a.dataset.s));
  if (!cur) return;
  const [c, k] = cur.split('/');
  try {
    const r = await api(`/api/table?country=${c}&comp=${k}`);
    $('#stb').innerHTML = tableHtml(r.rows, new Set());
  } catch(e){ $('#stb').innerHTML = '<div class="empty">مقدرتش أجيب الجدول.</div>'; }
}
function tableHtml(rows, mine){
  if (!rows || !rows.length) return '<div class="empty">مفيش جدول لده الدوري.</div>';
  return `<div class="sec" style="padding-inline:8px"><table class="tb"><tr><th>#</th><th style="text-align:start">الفريق</th><th>لعب</th><th>ف</th><th>ت</th><th>خ</th><th>فارق</th><th>نقاط</th></tr>
   ${rows.map(r => `<tr class="${mine.has(r.name)?'hl':''}"><td>${esc(r.rnk)}</td><td class="nm"><span>${logo('team', r.img, r.name_ar || r.name, 22)}${esc(r.name_ar || r.name)}</span></td><td>${esc(r.pld)}</td><td>${esc(r.w)}</td><td>${esc(r.d)}</td><td>${esc(r.l)}</td><td class="ltr">${esc(r.gd)}</td><td><b>${esc(r.pts)}</b></td></tr>`).join('')}</table></div>`;
}

/* ---------- صفحة الماتش ---------- */
const TABS = [['pred','التوقع'],['deep','تحليل شامل'],['sum','الأحداث'],['stats','إحصائيات'],['lu','التشكيلة'],['tbl','الترتيب'],['form','المواجهات']];
let mtab = null, mpath = null, mFresh = true;
async function viewMatch(path){
  clearTimer(); chrome('m');
  const sim = new URLSearchParams(location.search).get('sim');
  const ck = 'm' + path;
  if (mpath !== path){ mpath = path; mtab = null; mFresh = true; }
  window._render = m => render(m);
  function render(m){
    if (!mtab) mtab = m.status === 'FT' ? 'sum' : 'pred';
    $('#mtitle').textContent = m.league || 'تفاصيل الماتش';
    const started = m.score !== null;
    const st = {NS: kickStr(m.kickoff), FT: 'انتهى', HT: 'استراحة', LIVE: m.live_time || 'لايف'}[m.status];
    const tint = (c, a) => /^[0-9a-f]{6}$/i.test(c || '') ? '#' + c + a : '#00000000';
    let h = `<div class="hero" style="background:radial-gradient(70% 110% at 88% 0%,${tint(m.home_color,'24')},transparent 72%),radial-gradient(70% 110% at 12% 0%,${tint(m.away_color,'24')},transparent 72%),var(--card)"><div class="lgn">${esc(m.league)}${m.stage && m.stage !== m.league ? ' · ' + esc(m.stage) : ''}</div>
      <div class="main"><div class="tmx">${logo('team', m.home_badge, m.home, 60, m.home_color)}<span>${esc(m.home)}</span>${formDots(m,'home')}</div>
      <div class="mid"><div class="score">${started ? `<span>${m.score[0]}</span><i>-</i><span>${m.score[1]}</span>` : '<i>-</i>'}</div>
        <div class="st ${m.status==='LIVE'||m.status==='HT'?'live':''}">${m.status==='LIVE'?'<i>●</i> ':''}${esc(st)}</div>
        ${m.ht && started ? `<div class="st" style="margin-top:4px">الشوط الأول ${esc(m.ht[0])} - ${esc(m.ht[1])}</div>` : ''}</div>
      <div class="tmx">${logo('team', m.away_badge, m.away, 60, m.away_color)}<span>${esc(m.away)}</span>${formDots(m,'away')}</div></div></div>`;
    if (m.status !== 'FT') h += `<div class="acts"><button class="act ${isF(m.eid)?'on':''}" id="bellb">${BELL}<span>${isF(m.eid)?'بتابعه، هيوصلك كل جديد':'تابع الماتش وفعّل التنبيه'}</span></button><button class="act" id="deepb">🔎 ابحث عن أفضل توقع</button></div>`;
    h += '<div class="mtabs">' + TABS.map(([k,l]) => `<a data-k="${k}" class="${mtab===k?'on':''}">${l}</a>`).join('') + '</div>';
    h += `<div class="${mFresh && mtab==='pred' ? 'fresh' : ''}">` + ({pred:panePred, deep:paneDeep, sum:paneSum, stats:paneStats, lu:paneLu, tbl:paneTbl, form:paneForm}[mtab])(m) + '</div>';
    const y = scrollY; app.innerHTML = h; scrollTo(0, y);
    if (m.pred) mFresh = false;
    app.querySelectorAll('.mtabs a').forEach(a => a.onclick = () => { mtab = a.dataset.k; render(m); });
    const db = $('#deepb'); if (db) db.onclick = () => { mtab = 'deep'; render(m); };
    const bb = $('#bellb'); if (bb) bb.onclick = async () => { await toggleFollow(m); render(m); };
  }
  if (CACHE[ck]) render(CACHE[ck]); else app.innerHTML = skeleton(3);
  async function load(){
    try {
      const m = await api('/api/match?path=' + encodeURIComponent(path) + (sim ? '&sim=' + sim : ''));
      CACHE[ck] = m; render(m);
      if (m.status !== 'FT') timer = setTimeout(load, m.pred_state === 'pending' ? 2500 : (m.status === 'NS' ? 45000 : 8000));
    } catch(e){ if (!CACHE[ck]) app.innerHTML = '<div class="empty">مقدرتش أجيب بيانات الماتش، بحاول تاني...</div>'; timer = setTimeout(load, 6000); }
  }
  await load();
}
function x3(p, m){
  return `<div class="rings">${ring(p.H, {size:92, color:'var(--red)', label:'فوز ' + esc(m.home)})}${ring(p.D, {size:92, color:'var(--draw)', label:'تعادل'})}${ring(p.A, {size:92, color:'var(--away)', label:'فوز ' + esc(m.away)})}</div>`;
}
function pickBlock(m){
  const pk = m.pick_live || m.pick_pre;
  if (!pk || !pk.best) return `<div class="sec"><h3>أفضل اختيار</h3><div class="note">مفيش اختيار واضح دلوقتي: كل الاحتمالات تحت 50% أو الـodds أقل من 1.25.</div></div>`;
  const b = pk.best, a = pk.alt;
  return `<div class="sec"><h3>أفضل اختيار عند المحرك ${m.pick_live ? '<span class="tag">حي ويتحدث</span>' : ''}</h3>
    <div class="best">${ring(b.p, {size:104, color:'var(--red)'})}<div><div class="lab">${esc(b.label)}</div>
    <div class="kv"><div><b>${esc(b.grade)}</b><span>قوة الاختيار</span></div><div><b class="nn">${b.min_odds}</b><span>أقل odds للقيمة</span></div>${a ? `<div><b>${esc(a.label)}</b><span>البديل · ${pc(a.p)} · odds ${a.odds.toFixed(2)}</span></div>` : ''}</div></div></div>
    <div class="note" style="margin-top:14px">${b.proven ? 'نتيجة الماتش هي السوق الوحيد اللي ثبت بالاختبار الرجعي إن المحرك بيتفوق فيه على التخمين.' : 'أسواق الأهداف لسه ملهاش ميزة مثبتة، اعتبره تقدير مش أكتر.'} الـodds = ١ ÷ الاحتمال؛ لو odds شركة المراهنات أعلى من كده يبقى مجزي، لو أقل يبقى لأ.</div></div>`;
}
function panePred(m){
  if (m.status === 'FT') return '<div class="empty">الماتش خلص. التوقعات بتظهر قبل الماتش وأثناءه بس.</div>';
  const p = m.pred;
  if (!p){
    if (m.pred_state === 'failed') return '<div class="empty">مقدرتش أحسب توقع للماتش ده (بيانات الفريقين مش كفاية). بحاول تاني كل شوية.</div>';
    return `<div class="sec"><div class="wait"><span class="spin"></span>المحرك بيحسب توقع الماتش... ثواني</div><div class="skc"><i></i><i></i><i></i></div></div>`;
  }
  let h = pickBlock(m) + liveChart(m);
  if (m.live){
    const L = m.live;
    h += `<div class="sec"><h3>التوقع الحي <span class="tag">بيتحدث تلقائي</span></h3>${x3(L.x1x2, m)}<div style="height:22px"></div>
      <div class="rings">${ring(L.btts,{label:'كلا الفريقين يسجل'})}${ring(L.over['1.5'],{label:'أكتر من 1.5'})}${ring(L.over['2.5'],{label:'أكتر من 2.5'})}${ring(L.over['3.5'],{label:'أكتر من 3.5'})}
      </div>${L.fh ? `<div class="rings two" style="margin-top:20px">${ring(L.fh.o05,{label:'الشوط الأول أكتر من 0.5'})}${ring(L.fh.o15,{label:'الشوط الأول أكتر من 1.5'})}</div>` : ''}
      <div class="note" style="margin-top:14px">محسوب من الدقيقة والنتيجة والكروت الحمرا.</div></div>`;
  }
  h += `<div class="sec"><h3>نتيجة الماتش قبل ما يبدأ</h3>${x3(p.x1x2, m)}</div>`;
  h += '<details class="mored"><summary>كل الأسواق والتفاصيل</summary>';
  h += `<div class="sec"><h3>فرصة مزدوجة</h3><div class="rings">${ring(p.double['1X'],{label:'1X · ' + esc(m.home) + ' أو تعادل'})}${ring(p.double['12'],{label:'12 · مفيش تعادل'})}${ring(p.double['X2'],{label:'X2 · ' + esc(m.away) + ' أو تعادل'})}</div></div>`;
  h += `<div class="sec"><h3>الأهداف المتوقعة</h3><div class="xg"><div><b>${p.xg.home.toFixed(2)}</b><span>${esc(m.home)}</span></div><div><b>${p.xg.away.toFixed(2)}</b><span>${esc(m.away)}</span></div></div></div>`;
  h += `<div class="sec"><h3>أسواق الأهداف</h3><div class="rings">${ring(p.btts,{label:'كلا الفريقين يسجل'})}${ring(1-p.btts,{label:'كلا الفريقين مايسجلش'})}${ring(p.over['1.5'],{label:'أكتر من 1.5 هدف'})}
    ${ring(p.over['2.5'],{label:'أكتر من 2.5 هدف'})}${ring(1-p.over['2.5'],{label:'أقل من 2.5 هدف'})}${ring(p.over['3.5'],{label:'أكتر من 3.5 هدف'})}</div></div>`;
  h += `<div class="sec"><h3>الشوط الأول</h3><div class="rings two">${ring(p.fh.o05,{label:'أكتر من 0.5 هدف'})}${ring(p.fh.o15,{label:'أكتر من 1.5 هدف'})}</div></div>`;
  h += `<div class="sec"><h3>أكتر النتايج احتمالاً</h3><div class="rings" style="grid-template-columns:repeat(3,1fr)">${p.top_scores.slice(0,3).map(([s,v]) => ring(v,{size:76, color:'var(--red)', label:`<span class="ltr">${esc(s)}</span>`})).join('')}</div></div>`;
  h += `<div class="sec"><h3>عن التوقع</h3><div class="note">دقة التوقع: ${esc(p.confidence)}. الموديل Poisson + Dixon-Coles مع قوة الخصم وآخر الماتشات. بيتفوق على التخمين في نتيجة الماتش (1X2) بس، وأسواق الأهداف وكلا الفريقين قريبة من متوسط الدوري، والشوط الأول 0.5 مفيش فيه ميزة مثبتة. الدايرة الحمرا = احتمال 50% أو أكتر. الاحتمال مش ضمان.</div></div>`;
  return h + '</details>';
}
function evMark(e){
  const g = '<i class="ic g"></i>', y = '<i class="ic y"></i>', r = '<i class="ic r"></i>', x = '<i class="ic x"></i>';
  return {goal:[g,''], pen_goal:[g,' (ركلة جزاء)'], own_goal:[g,' (هدف عكسي)'], yellow:[y,''], red:[r,''], second_yellow:[y+r,' (إنذار تاني)'],
          goal_cancelled:[x,' (هدف ملغي)'], pen_miss:[x,' (ركلة جزاء ضايعة)']}[e.kind] || ['',''];
}
function paneSum(m){
  const ev = (m.incidents || []).filter(e => e.kind !== 'sub');
  if (!ev.length) return `<div class="empty">${m.status === 'NS' ? 'الماتش لسه ما بدأش.' : 'مفيش أحداث لحد دلوقتي.'}</div>`;
  let h = liveChart(m) + '<div class="sec">', half = 0;
  for (const e of ev){
    if (e.half !== half){ if (half) h += '<div class="sep">الاستراحة</div>'; half = e.half; }
    const [ic, tx] = evMark(e), t = (e.min ?? '') + (e.extra ? '+' + e.extra : '') + "'";
    const body = `<span class="who">${ic}<span>${esc(e.player)}${tx}</span></span>${e.score ? `<small class="ltr">${esc(e.score.away)} - ${esc(e.score.home)}</small>` : ''}${e.assist ? `<small>صناعة: ${esc(e.assist)}</small>` : ''}${e.var ? `<small>${esc(e.var)}</small>` : ''}`;
    h += `<div class="ev"><div class="l">${e.side==='home'?body:''}</div><div class="m">${t}</div><div class="r">${e.side==='away'?body:''}</div></div>`;
  }
  return h + '</div>';
}
const STAT_LABELS = [['expectedGoals','الأهداف المتوقعة (xG)',1],['possession','الاستحواذ %',0],['shotsOnTarget','تسديدات على المرمى',0],['shotsOffTarget','تسديدات خارج المرمى',0],
  ['shotsBlocked','تسديدات محجوبة',0],['corners','ركنيات',0],['offsides','تسلل',0],['fouls','أخطاء',0],['yellowCards','كروت صفراء',0],['redCards','كروت حمراء',0],
  ['crosses','عرضيات',0],['goalkeeperSaves','تصديات الحارس',0],['throwIns','رميات تماس',0],['goalKicks','ضربات مرمى',0]];
function paneStats(m){
  const s = m.stats;
  if (!s) return `<div class="empty">${m.status === 'NS' ? 'الإحصائيات بتظهر لما الماتش يبدأ.' : 'مفيش إحصائيات متاحة.'}</div>`;
  let h = '<div class="sec">';
  for (const [k, lab, dec] of STAT_LABELS){
    const v = s[k]; if (!v || v.length < 2) continue;
    const tot = (+v[0] || 0) + (+v[1] || 0), a = tot ? (+v[0]/tot*100) : 50, f = x => dec ? Number(x).toFixed(2) : x;
    h += `<div class="stat"><div class="h"><b>${f(v[0])}</b><span class="lb">${lab}</span><b>${f(v[1])}</b></div>
      <div class="b"><i style="width:${a}%;background:var(--red)"></i><i style="width:${100-a}%;background:var(--away)"></i></div></div>`;
  }
  return h + '</div>';
}
function paneLu(m){
  const L = m.lineups;
  if (!L) return '<div class="empty">التشكيلة لسه ما نزلتش (بتنزل قبل الماتش بحوالي ساعة).</div>';
  const col = (t, name, img, color) => !t ? '' : `<div><h4>${logo('team', img, name, 24, color)}<span>${esc(name)} · <span class="ltr">${esc(t.formation)}</span></span></h4>${t.starters.map(p => `<div class="p"><b>${esc(p.num ?? '')}</b><span>${esc(p.name)}</span></div>`).join('')}
    <h4 style="margin-top:16px;color:var(--mut)">البدلاء</h4>${t.subs.map(p => `<div class="p"><b>${esc(p.num ?? '')}</b><span>${esc(p.name)}</span></div>`).join('')}
    ${t.coach ? `<div class="note" style="margin-top:10px">المدرب: ${esc(t.coach)}</div>` : ''}</div>`;
  return `<div class="sec"><div class="lu">${col(L.home, m.home, m.home_badge, m.home_color)}${col(L.away, m.away, m.away_badge, m.away_color)}</div></div>`;
}
const paneTbl = m => tableHtml(m.table, new Set([m.home_en, m.away_en]));
function paneForm(m){
  const F = m.form; if (!F) return '<div class="empty">مفيش بيانات مواجهات.</div>';
  const list = (arr, title) => `<div class="sec"><h3>${title}</h3>${arr.length ? arr.map(e => `<div class="fm"><span class="dt">${esc(e.date.slice(6,8)+'/'+e.date.slice(4,6)+'/'+e.date.slice(2,4))}</span><span>${esc(e.home)} <b class="ltr">${esc(e.as)} - ${esc(e.hs)}</b> ${esc(e.away)}</span></div>`).join('') : '<div class="note">مفيش.</div>'}</div>`;
  return list(F.home, 'آخر ماتشات ' + esc(m.home)) + list(F.away, 'آخر ماتشات ' + esc(m.away)) + list(F.h2h, 'المواجهات المباشرة');
}

/* ---------- Router ---------- */
function go(){
  scrollTo(0,0);
  const h = location.hash.replace(/^#\/?/, '');
  if (h.startsWith('m/')) return viewMatch(h.slice(2));
  if (h === 'picks') return viewList('picks');
  if (h === 'track') return viewTrack();
  if (h === 'standings') return viewStandings();
  viewList('');
}

/* ===== v5: تطبيق PWA + متابعة الماتشات + إشعارات + سجل الدقة + مسار الاحتمالات ===== */
const FK = 'kl_f5', NP = () => 'Notification' in window ? Notification.permission : 'denied';
const gF = () => { try { return JSON.parse(localStorage.getItem(FK) || '{}'); } catch(e){ return {}; } };
const sF = f => { try { localStorage.setItem(FK, JSON.stringify(f)); } catch(e){} };
const isF = id => !!gF()[id];
const kEpoch = v => { const s = String(v || ''); return s.length >= 14 ? Date.UTC(+s.slice(0,4), +s.slice(4,6)-1, +s.slice(6,8), +s.slice(8,10), +s.slice(10,12)) / 1000 : +s || 0; };
const BELL = '<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M6 8a6 6 0 0112 0c0 7 3 8 3 8H3s3-1 3-8M10 20a2 2 0 004 0"/></svg>';
const bellBtn = m => (m.status === 'FT' || m.status === 'OFF') ? '' : `<button class="bell ${isF(m.eid)?'on':''}" data-b="${m.eid}" aria-label="تنبيه">${BELL}</button>`;
function toast(t, u){ const d = document.createElement('div'); d.className = 'toast'; d.textContent = t; d.onclick = () => { d.remove(); if (u) location.hash = u; }; document.body.appendChild(d); setTimeout(() => d.remove(), 5500); }
async function notify(t, b, u){
  toast(t + ' · ' + b, u);
  if (NP() !== 'granted') return;
  try { const r = await navigator.serviceWorker.getRegistration(), o = {body: b, icon: '/icon-192.png', badge: '/icon-192.png', lang: 'ar', dir: 'rtl', tag: u + '|' + b, vibrate: [150,80,150], data: {url: u}}; r ? r.showNotification(t, o) : new Notification(t, o); } catch(e){}
}
async function toggleFollow(m){
  const f = gF();
  if (f[m.eid]){ delete f[m.eid]; sF(f); return toast('اتلغت متابعة الماتش'); }
  f[m.eid] = {eid: m.eid, path: m.path, home: m.home_ar || m.home, away: m.away_ar || m.away, k: kEpoch(m.kickoff), n: {}, l: null}; sF(f);
  if (NP() === 'default') await Notification.requestPermission();
  toast(NP() === 'granted' ? 'تمام، هتوصلك إشعارات: قبل البداية، الأهداف، الكروت الحمرا، النهاية' : 'المتابعة شغالة جوه التطبيق بس. فعّل الإشعارات من إعدادات المتصفح');
  tick();
}
let ticking = false;
async function tick(){
  const F = gF(), ids = Object.keys(F); if (!ids.length || ticking) return; ticking = true;
  try {
    const now = Date.now() / 1000, live = [];
    for (const id of ids){ const f = F[id];
      if (f.k && !f.n.r && f.k - now <= 900 && f.k - now > 0){ f.n.r = 1; notify('الماتش هيبدأ كمان شوية', f.home + ' × ' + f.away, '#/m/' + f.path); }
      if (!f.k || f.k - now < 1800 || f.l) live.push(f); }
    if (live.length){
      const r = await api('/api/watch?ids=' + encodeURIComponent(live.map(f => f.path).join(',')));
      for (const w of r.matches){ const f = F[w.eid]; if (!f) continue;
        const u = '#/m/' + f.path, n = w.home + ' ' + w.score[1] + ' - ' + w.score[0] + ' ' + w.away, l = f.l, g = w.score[0] + w.score[1];
        if (l){
          if (l.s === 'NS' && w.status === 'LIVE') notify('بدأ الماتش', w.home + ' × ' + w.away, u);
          if (g > l.g) notify('جوووول! ' + (w.last && w.last.player ? w.last.player + ' ' + (w.last.min || '') + "'" : ''), n, u);
          if (w.reds > l.r) notify('كارت أحمر', n, u);
          if (w.status === 'HT' && l.s !== 'HT') notify('نهاية الشوط الأول', n, u);
          if (w.status === 'FT' && l.s !== 'FT') notify('انتهى الماتش', n, u);
        }
        f.l = {s: w.status, g, r: w.reds};
        if (w.status === 'FT') delete F[w.eid];
      }
    }
    sF(F);
  } catch(e){} finally { ticking = false; }
}
setInterval(tick, 15000); addEventListener('load', () => setTimeout(tick, 1500)); document.addEventListener('visibilitychange', () => document.visibilityState === 'visible' && tick());
if ('serviceWorker' in navigator) addEventListener('load', () => navigator.serviceWorker.register('/sw.js').catch(() => {}));
let dip = null; const standalone = () => matchMedia('(display-mode: standalone)').matches || navigator.standalone;
addEventListener('beforeinstallprompt', e => { e.preventDefault(); dip = e; }); addEventListener('appinstalled', () => { dip = null; toast('اتثبّت التطبيق'); });
function openMore(){
  const f = Object.values(gF()), np = NP(), ios = /iphone|ipad/i.test(navigator.userAgent), sh = $('#sheet');
  sh.innerHTML = `<div class="grab"></div>
  <div class="mrow"><div><b>تثبيت كتطبيق</b><small>${standalone() ? 'شغال كتطبيق دلوقتي' : dip ? 'بيفتح من الشاشة الرئيسية من غير شريط المتصفح' : ios ? 'من زر المشاركة اختار «إضافة إلى الشاشة الرئيسية»' : 'من قايمة المتصفح اختار «تثبيت التطبيق» (محتاج HTTPS)'}</small></div>${dip && !standalone() ? '<button class="btn" id="inst">تثبيت</button>' : ''}</div>
  <div class="mrow"><div><b>الإشعارات</b><small>${np === 'granted' ? 'مفعّلة. اضغط 🔔 على أي ماتش عشان تتابعه' : np === 'denied' ? 'متقفلة من إعدادات المتصفح' : 'مش مفعّلة'}</small></div>${np === 'granted' ? '<button class="btn g" id="tn">تجربة</button>' : np === 'default' ? '<button class="btn" id="en">تفعيل</button>' : ''}</div>
  <div class="sh" style="padding:14px 8px 4px">ماتشات بتابعها (${f.length})</div>
  ${f.map(x => `<div class="mrow"><div><b>${esc(x.home)} × ${esc(x.away)}</b></div><button class="btn g" data-u="${x.eid}">إلغاء</button></div>`).join('') || '<div class="note" style="padding:6px 10px">اضغط 🔔 في أي ماتش عشان توصلك إشعاراته.</div>'}
  <div class="note" style="padding:12px 10px 0">الإشعارات بتشتغل والتطبيق مفتوح أو في الخلفية. للإشعار والتطبيق مقفول محتاج سيرفر Push على HTTPS.</div>`;
  sh.style.display = $('#shade').style.display = 'block';
  const q = s => sh.querySelector(s);
  if (q('#inst')) q('#inst').onclick = () => { dip.prompt(); closeSheet(); };
  if (q('#en')) q('#en').onclick = async () => { await Notification.requestPermission(); openMore(); };
  if (q('#tn')) q('#tn').onclick = () => { closeSheet(); notify('كورة لايف', 'الإشعارات شغالة تمام', '#/'); };
  sh.querySelectorAll('[data-u]').forEach(b => b.onclick = () => { const F = gF(); delete F[b.dataset.u]; sF(F); openMore(); });
}
async function viewTrack(){
  clearTimer(); chrome('track'); app.innerHTML = skeleton(3);
  try {
    const t = await api('/api/track'), b = (x, l) => `<div><b>${x}</b><span>${l}</span></div>`;
    let h = '<div class="hint">سجل أمين لتوقعات المحرك: بنسجل التوقع قبل الماتش ونقارنه بالنتيجة بعد ما يخلص، من غير أي تعديل.</div>';
    if (!t.n) h += `<div class="empty">لسه مفيش ماتشات اتحسمت. السجل بيتملي لوحده أول ما الماتشات اللي اتوقعناها تخلص${t.pending ? ' (' + t.pending + ' ماتش مستنيين)' : ''}.</div>`;
    else {
      h += `<div class="sec"><h3>الأداء الإجمالي <span class="tag">${t.n} ماتش</span></h3><div class="xg">${b(t.acc + '%', 'نتيجة الماتش صح')}${b(t.pick_hit == null ? '—' : t.pick_hit + '%', 'أفضل اختيار صح')}${b(t.brier, 'Brier (التخمين 0.667)')}</div>
        ${t.pick_exp != null ? `<div class="note" style="margin-top:14px">متوسط احتمال الاختيارات كان ${t.pick_exp}% والفعلي ${t.pick_hit}%${t.hi_n ? '، واللي فوق 60% (' + t.hi_n + ' ماتش) نجحت ' + t.hi_hit + '%' : ''}. لو الرقمين قريبين يبقى المحرك مظبوط.</div>` : ''}</div>`;
      h += '<div class="sec"><h3>آخر النتايج</h3>' + t.recent.map(r => `<div class="fm" style="grid-template-columns:1fr auto"><span>${esc(r.home)} <b class="ltr">${r.s[1]} - ${r.s[0]}</b> ${esc(r.away)}<small style="display:block;color:var(--mut)">${esc(r.league || '')} · توقعنا ${P(r.x[0])}/${P(r.x[1])}/${P(r.x[2])}${r.pick ? ' · ' + esc(r.pick) + (r.pk ? ' ✓' : ' ✗') : ''}</small></span><b style="color:${r.ok1 ? 'var(--acc)' : 'var(--live)'}">${r.ok1 ? '✓' : '✗'}</b></div>`).join('') + '</div>';
    }
    app.innerHTML = h;
  } catch(e){ app.innerHTML = '<div class="empty">مقدرتش أجيب السجل.</div>'; }
}
function liveChart(m){
  const h = m.hist; if (!h || h.length < 3 || !m.pred) return '';
  const x0 = m.pred.x1x2, pts = [[0, x0.H, x0.D, x0.A, 0, 0], ...h];
  const X = v => 12 + Math.min(v, 95) / 95 * 336, Y = v => 128 - v * 116, L = i => pts.map(p => X(p[0]).toFixed(1) + ',' + Y(p[i]).toFixed(1)).join(' ');
  const gs = []; for (let i = 1; i < pts.length; i++) if (pts[i][4] + pts[i][5] > pts[i-1][4] + pts[i-1][5]) gs.push(pts[i]);
  return `<div class="sec"><h3>مسار الاحتمالات في الماتش</h3><svg viewBox="0 0 360 140" style="width:100%;direction:ltr">
    <g stroke="var(--line)">${[.25,.5,.75].map(v => `<line x1="12" x2="348" y1="${Y(v)}" y2="${Y(v)}"/>`).join('')}<line x1="${X(45)}" x2="${X(45)}" y1="8" y2="128" stroke-dasharray="3 4"/></g>
    <polyline points="${L(2)}" fill="none" stroke="var(--draw)" stroke-width="1.6" stroke-dasharray="4 3"/><polyline points="${L(3)}" fill="none" stroke="var(--away)" stroke-width="2.2"/><polyline points="${L(1)}" fill="none" stroke="var(--acc)" stroke-width="2.6"/>
    ${gs.map(p => `<circle cx="${X(p[0])}" cy="${Y(p[1])}" r="4.5" fill="var(--bg)" stroke="#fff" stroke-width="2"/>`).join('')}</svg>
    <div class="lgd"><span style="color:var(--acc)">● ${esc(m.home)}</span><span style="color:var(--draw)">● تعادل</span><span>● ${esc(m.away)}</span></div><div class="note" style="margin-top:8px">الدواير البيضا = أهداف. الخط بيبدأ من التوقع قبل الماتش.</div></div>`;
}

/* ===== v6: المفضلة، شريط التواريخ، شغال دلوقتي، نقط الفورمة ===== */
state.pf = 'all';
const STAR = '<svg class="ic" width="26" height="26" viewBox="0 0 24 24" fill="#e8b93a"><path d="M12 2.5l2.9 6.2 6.6.8-4.9 4.6 1.3 6.7L12 17.5 6.1 20.8l1.3-6.7L2.5 9.5l6.6-.8z"/></svg>';
const LIVEDOT = '<span class="ic" style="width:26px;height:26px;display:grid;place-items:center"><i style="width:10px;height:10px;border-radius:50%;background:var(--live)"></i></span>';
const PIN = /مصر|egypt|السعود|saudi|أبطال|champions|إنجلترا|england|إسبانيا|spain|إيطاليا|italy|ألمانيا|germany|فرنسا|france/i;
const pfOk = m => { const b = m.pick.best, k = state.pf; return k === 'all' || (k === 'res' && b.proven) || (k === 'goals' && !b.proven) || (k === 'strong' && b.p >= .66); };
function buildGroups(list){
  const isL = m => m.status === 'LIVE' || m.status === 'HT', fav = list.filter(m => isF(m.eid)), rest = list.filter(m => !isF(m.eid));
  const lv = state.live ? [] : rest.filter(isL), rr = state.live ? rest : rest.filter(m => !isL(m));
  const pr = m => PIN.test([m.country_ar, m.country_name, m.league_ar, m.league].join(' ')) ? 0 : 1;
  const sorted = rr.map((m, i) => [m, i]).sort((a, b) => pr(a[0]) - pr(b[0]) || a[1] - b[1]).map(x => x[0]), out = [];
  if (fav.length) out.push({key: 'fav', name: 'المفضلة', country: '', badge: null, m: fav});
  if (lv.length) out.push({key: 'live', name: 'شغال دلوقتي', country: lv.length + ' ماتش', badge: null, m: lv});
  return out.concat(groupBy(sorted));
}
function dayStrip(){
  const t = ymd(new Date()); let h = '<div class="dstrip" id="dstrip">';
  for (let i = -3; i <= 7; i++){ const s = shiftDate(t, i), d = parseYmd(s), w = i === 0 ? 'النهارده' : i === 1 ? 'بكرة' : i === -1 ? 'امبارح' : d.toLocaleDateString('ar-EG-u-nu-latn', {weekday: 'short'});
    h += `<a class="dchip ${s === state.date && !state.live ? 'on' : ''}" data-d="${s}"><small>${w}</small><b>${d.getDate()}</b></a>`; }
  return h + '</div>';
}
function formDots(m, side){
  const arr = (m.form && m.form[side]) || [], me = side === 'home' ? m.home_en : m.away_en;
  if (!arr.length) return '';
  return '<div class="fd">' + arr.slice(0, 5).reverse().map(e => { const h = e.home === me, gf = +(h ? e.hs : e.as), ga = +(h ? e.as : e.hs); return `<i class="${gf > ga ? 'w' : gf < ga ? 'l' : 'd'}"></i>`; }).join('') + '</div>';
}

/* ===== v7: التحليل الشامل ===== */
const DEEP = {}, TIER = {data: 'مبني على بيانات', est: 'تقدير تقريبي', live: 'حي من الماتش'};
function paneDeep(m){
  if (m.status === 'FT') return '<div class="empty">الماتش خلص.</div>';
  const d = DEEP[m.path];
  if (!d || (!d.busy && Date.now() - d.t > (m.status === 'NS' ? 60000 : 3000))){
    DEEP[m.path] = Object.assign(d || {}, {busy: true});
    api('/api/deep?path=' + encodeURIComponent(m.path)).then(r => { DEEP[m.path] = {t: Date.now(), r}; if (mtab === 'deep' && mpath === m.path && window._render) window._render(CACHE['m' + m.path]); })
      .catch(() => { DEEP[m.path] = {t: Date.now(), r: {state: 'err'}}; });
  }
  const r = d && d.r;
  if (!r) return '<div class="sec"><div class="wait"><span class="spin"></span>بيدوّر على أفضل التوقعات في كل الأسواق...</div></div>';
  if (r.state !== 'ok') return `<div class="empty">${r.state === 'pending' ? 'المحرك لسه بيحسب توقع الماتش، جرب بعد ثواني.' : 'مقدرتش أعمل التحليل دلوقتي.'}</div>`;
  let h = `<div class="sec"><h3>أفضل توقعات الماتش ${r.live ? '<span class="tag">حي</span>' : ''}</h3>${r.top.map(t => `<div class="dr"><span>${esc(t.label)}<small>${esc(t.sec)} · odds ${t.odds.toFixed(2)}</small></span><b>${P(t.p)}%</b><div class="b"><i style="width:${P(t.p)}%"></i></div></div>`).join('') || '<div class="note">مفيش توقع واضح فوق 55%.</div>'}</div>`;
  for (const s of r.secs) h += `<div class="sec"><h3>${esc(s.t)} <span class="tag ${s.tier}">${TIER[s.tier]}</span></h3>${s.items.map(([l, p]) => `<div class="dr"><span>${esc(l)}</span><b>${P(p)}%</b><div class="b"><i style="width:${P(p)}%;${p < .5 ? 'background:var(--draw)' : ''}"></i></div></div>`).join('')}<div class="note" style="margin-top:10px">${esc(s.note)}</div></div>`;
  return h + '<div class="note" style="padding:12px 16px">الأهداف هي الأدق لأنها مبنية على بيانات الفرق. الركنيات والكروت والتسديدات قبل الماتش تقدير بمتوسطات عامة، وبتتظبط على الماتش نفسه أول ما يبدأ. كلها احتمالات مش ضمانات.</div>';
}
addEventListener('hashchange', go);
(async () => { try { CFG = Object.assign(CFG, await api('/api/cfg')); } catch(e){} go(); })();
</script>
</body>
</html>
'''


@route("/")
def index():
    return "text/html; charset=utf-8", INDEX_HTML.encode("utf-8")


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def do_GET(self):
        u = urlparse(self.path)
        _tl.args = {k: v[0] for k, v in parse_qs(u.query).items()}
        try:
            if u.path in ROUTES:
                ctype, body = ROUTES[u.path]()
                code = 200
            else:
                ctype, body, code = "text/plain; charset=utf-8", b"not found", 404
        except Exception as e:  # noqa: BLE001
            log("خطأ", u.path, repr(e)[:150])
            ctype, body, code = "application/json; charset=utf-8", json.dumps({"error": str(e)}).encode(), 500
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)


if __name__ == "__main__":
    threading.Thread(target=worker, daemon=True).start()
    log("شغّال على http://localhost:%d" % PORT)
    ThreadingHTTPServer(("0.0.0.0", PORT), Handler).serve_forever()
