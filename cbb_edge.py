#!/usr/bin/env python3
"""
CBB Edge: a repeatable men's college basketball betting dashboard.

Pulls box scores, schedules and sportsbook lines from free public sources (ESPN's public
API and the sportsdataverse data releases on GitHub), models every Division I game for the
next 7 days and writes a self-contained HTML dashboard:

  * moneyline, spread, total, team totals and 1st half markets with fair odds and a
    "bet at" price for each
  * player projections (points, rebounds, assists, threes, PRA) from projected minutes
  * players missing recent games (college has no public injury report)
  * records, conference standings, AP rank, trends, ATS / over-under records, stat ranks
  * a Top bets tab (best bets of the week) and a Track record tab

Run:  python cbb_edge.py            (builds the board and publishes it to GitHub Pages)
      python cbb_edge.py --open     (also opens it in your browser)
      python cbb_edge.py --help     (all options)
"""

import argparse
import csv
import datetime as dt
import html as htmlmod
import json
import math
import os
import re
import shutil
import subprocess
import sys
import time
import unicodedata
import webbrowser
from concurrent.futures import ThreadPoolExecutor

import numpy as np
import requests

try:
    import pyarrow.parquet as pq
except ImportError:  # handled at runtime with a clear message
    pq = None

HERE = os.path.dirname(os.path.abspath(__file__))

# --------------------------------------------------------------------------
# Settings
# --------------------------------------------------------------------------
CONFIG = {
    "data_dir": "cbb_data",
    "out": "cbb_dashboard.html",
    "days": 7,                    # today + the next 6 days (the betting week)
    "workers": 8,
    # ---- team model (tuned on 2025-26 with walk-forward tests, see "How it works") ----
    "hl_days": 45,                # half-life (days) for weighting games in team ratings
    "prior_games": 5,             # how many games of evidence the preseason rating is worth
    "prior_regress": 0.60,        # last season's rating (vs its conference average) carried over
    "conf_regress": 1.0,          # conference strength carried over (backtest: no pull to average)
    "pace_prior_regress": 0.75,
    "roster_shift_w": 1.2,        # share of the returning/transfer value change added to the prior
    "hca": 4.4,                   # home-court edge in points per 100 possessions (refit each run)
    "b2b": 0.0,
    # Model share of the betting estimate when a line is posted. 15-25% was the most accurate blend in the
    # 2025-26 test, but 35% / 25% with the gap caps below picked winners at closing prices (see How it works).
    "w_model_margin": 0.35,
    "w_model_total": 0.25,
    "sd_margin": 11.0,            # spread of results around the blended estimate (2025-26)
    "sd_total": 16.9,
    "sd_team": 10.5,
    "share_1h": 0.4675, "margin_1h": 0.574, "sd_1h_margin": 9.3, "sd_1h_total": 10.4,
    "nond1_rating": -18.0,        # non-Division I opponents, margin points vs an average D1 team
    # ---- player availability (college has no public injury report) ----
    "inj_k": 0.33,                # margin points per 40 min per point of game score/40 above replacement
    "inj_repl": 8.0,              # replacement-level game score per 40 minutes
    "missed_min_mpg": 15.0,       # a rotation player (15+ mpg) who missed the team's last game(s) is flagged
    "missed_play_prob": {1: 0.55, 2: 0.25, 3: 0.12},   # chance he plays after missing 1 / 2 / 3+ straight games
    "status_play": {"out": 0.0, "suspension": 0.0, "doubtful": 0.2, "questionable": 0.5,
                    "day-to-day": 0.7, "probable": 0.93},
    # ---- players ----
    "player_hl_games": 10,
    "minutes_hl_games": 5,
    "last_season_player_weight": 0.45,
    "min_proj_minutes": 15,
    "max_minutes": 38.0,
    "max_line_fetch": 250,        # past-game summaries fetched per run to fill in closing lines
    "min_scale_alpha": 0.4,
    "prop_var_mult": 1.3,
    "prop_mean_cv": {"pts": 0.22, "fg3m": 0.22, "default": 0.17},
    "prop_bias": {},
    # ---- odds ----
    "buffer_main": 0.02,
    "buffer_total": 0.035,        # game totals: the market beat the model on totals, so they need a bigger edge
    "buffer_derived": 0.035,
    "buffer_props": 0.045,
    # ---- top bets ----
    "top_bets_max": 10,
    "top_bets_min": 5,
    "high_prob_min": 0.58,
    "min_prob": 0.40,
    "max_market_gap": 0.12,       # props: model vs market win-probability gap (+5 pts) that signals news
    "max_gap_pts": 6.0,           # sides: skip when the model alone is 6+ points off the market spread
    "max_gap_pts_total": 9.0,     # totals: skip when the model alone is 9+ points off the market total
    "max_per_game": 2,
    "max_props_top": 3,
    "min_ev_top": 0.015,
    "max_fav_top": -400,
    # ---- publishing (set "repo_url" to "" to turn publishing off) ----
    "repo_url": "https://github.com/HalfWitty/CBBDashboard.git",
    "site_dir": "cbb_site",
    "branch": "main",
}

ESPN_SITE = "https://site.api.espn.com/apis/site/v2/sports/basketball/mens-college-basketball"
ESPN_CORE = "https://sports.core.api.espn.com/v2/sports/basketball/leagues/mens-college-basketball"
REL = "https://github.com/sportsdataverse/sportsdataverse-data/releases/download"
REL_FILES = {
    "player": "espn_mens_college_basketball_player_boxscores/player_box_{s}.parquet",
    "team": "espn_mens_college_basketball_team_boxscores/team_box_{s}.parquet",
    "sched": "espn_mens_college_basketball_schedules/mbb_schedule_{s}.parquet",
}

CONF_NAMES = {  # ESPN conference id -> (short name, full name)
    1: ("Am. East", "America East"), 2: ("ACC", "Atlantic Coast"), 3: ("A-10", "Atlantic 10"),
    4: ("Big East", "Big East"), 5: ("Big Sky", "Big Sky"), 6: ("Big South", "Big South"),
    7: ("Big Ten", "Big Ten"), 8: ("Big 12", "Big 12"), 9: ("Big West", "Big West"), 10: ("CAA", "Coastal Athletic"),
    11: ("CUSA", "Conference USA"), 12: ("Ivy", "Ivy League"), 13: ("MAAC", "Metro Atlantic"),
    14: ("MAC", "Mid-American"), 16: ("MEAC", "Mid-Eastern"), 18: ("MVC", "Missouri Valley"),
    19: ("NEC", "Northeast"), 20: ("OVC", "Ohio Valley"), 21: ("Pac-12", "Pac-12"), 22: ("Patriot", "Patriot League"),
    23: ("SEC", "Southeastern"), 24: ("SoCon", "Southern"), 25: ("Southland", "Southland"),
    26: ("SWAC", "Southwestern"), 27: ("Sun Belt", "Sun Belt"), 29: ("WCC", "West Coast"), 30: ("WAC", "Western Athletic"),
    43: ("Indep.", "Independents"), 44: ("Mountain West", "Mountain West"), 45: ("Horizon", "Horizon League"),
    46: ("ASUN", "Atlantic Sun"), 49: ("Summit", "Summit League"), 62: ("American", "American"),
}
NOND1 = 0   # every non-Division I opponent shares this team id in the model

DIRS = {}
LOG_FIELDS = ["run_ts", "game_id", "date", "away", "home", "market", "label", "line", "prob",
              "fair", "book_odds", "book_line", "kind"]
OFFLINE = False


def log(msg):
    print(msg, flush=True)


def txt(x):
    return "" if x is None else str(x)


def esc(x):
    return htmlmod.escape(txt(x), quote=True)


def fnum(x, default=None):
    try:
        if x is None or x == "":
            return default
        v = float(str(x).replace("+", ""))
        return v if math.isfinite(v) else default
    except (TypeError, ValueError):
        return default


# --------------------------------------------------------------------------
# Time helpers (Eastern time without needing tz databases)
# --------------------------------------------------------------------------
def _et_offset(utc):
    y = utc.year
    m = dt.datetime(y, 3, 8)
    start = (m + dt.timedelta(days=(6 - m.weekday()) % 7)).replace(hour=7)
    n = dt.datetime(y, 11, 1)
    end = (n + dt.timedelta(days=(6 - n.weekday()) % 7)).replace(hour=6)
    return -4 if start <= utc < end else -5


def parse_utc(s):
    if not s:
        return None
    s = str(s).replace("Z", "")
    for f in ("%Y-%m-%dT%H:%M:%S", "%Y-%m-%dT%H:%M", "%Y-%m-%d %H:%M:%S"):
        try:
            return dt.datetime.strptime(s[:19] if f.endswith("%S") else s[:16], f)
        except ValueError:
            continue
    return None


def to_et(utc):
    return utc + dt.timedelta(hours=_et_offset(utc)) if utc else None


def now_et():
    return to_et(dt.datetime.now(dt.timezone.utc).replace(tzinfo=None))


def season_for(d):
    """ESPN season year: the 2026-27 season is 2027."""
    return d.year + 1 if d.month >= 8 else d.year


def ddate(s):
    return dt.date.fromisoformat(str(s)[:10])


def fmt_time(utc):
    e = to_et(utc)
    if not e:
        return "TBD"
    h = e.hour % 12 or 12
    return f"{h}:{e.minute:02d} {'AM' if e.hour < 12 else 'PM'} ET"


# --------------------------------------------------------------------------
# HTTP with on-disk cache
# --------------------------------------------------------------------------
class Api:
    def __init__(self):
        self.s = requests.Session()
        self.s.headers.update({"User-Agent": "Mozilla/5.0 (cbb-edge dashboard)"})
        self.fails = 0

    def _fresh(self, path, max_age):
        return path and os.path.exists(path) and (max_age is None or time.time() - os.path.getmtime(path) < max_age)

    def get_bytes(self, url, path, max_age=None, tries=3, timeout=60):
        if self._fresh(path, max_age) or (OFFLINE and path and os.path.exists(path)):
            with open(path, "rb") as f:
                return f.read()
        if OFFLINE:
            return None
        for i in range(tries):
            try:
                r = self.s.get(url, timeout=timeout)
                if r.status_code == 200 and r.content:
                    if path:
                        tmp = path + ".tmp"
                        with open(tmp, "wb") as f:
                            f.write(r.content)
                        os.replace(tmp, path)
                    return r.content
                if r.status_code in (400, 404):
                    break
            except requests.RequestException:
                pass
            time.sleep(1.5 * (i + 1))
        self.fails += 1
        if path and os.path.exists(path):  # stale copy beats nothing
            with open(path, "rb") as f:
                return f.read()
        return None

    def get(self, url, path=None, max_age=None, tries=3, timeout=30):
        b = self.get_bytes(url, path, max_age, tries, timeout)
        if b is None:
            return None
        try:
            return json.loads(b)
        except ValueError:
            return None


def jdump(obj, path):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, separators=(",", ":"))
    os.replace(tmp, path)


def jload(path, default=None):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


# --------------------------------------------------------------------------
# Odds math
# --------------------------------------------------------------------------
def am_dec(a):
    return 1 + a / 100 if a > 0 else 1 + 100 / abs(a)


def dec_am(d):
    if d is None or d <= 1.0001:
        return None
    return int(round((d - 1) * 100)) if d >= 2 else int(round(-100 / (d - 1)))


def fmt_am(a):
    if a is None:
        return "–"
    return f"+{a}" if a > 0 else str(a)


def parse_am(v):
    """American odds from an int, '+150', '-110', 'EVEN', or decimal odds like 1.91."""
    if v is None or v == "":
        return None
    if isinstance(v, (int, float)):
        x = float(v)
    else:
        t = str(v).strip().upper().replace("−", "-")
        if t in ("EVEN", "EV", "PK", "PICK"):
            return 100
        try:
            x = float(t.replace("+", ""))
        except ValueError:
            return None
    if not math.isfinite(x):
        return None
    if abs(x) >= 100:
        return int(round(x))
    if 1.01 <= x < 50:
        return dec_am(x)
    return None


def parse_line(v):
    if v is None:
        return None
    if isinstance(v, (int, float)):
        return float(v)
    t = str(v).strip().upper()
    if t in ("PK", "PICK", "EVEN"):
        return 0.0
    m = re.search(r"[-+]?\d+(?:\.\d+)?", t)
    return float(m.group()) if m else None


def fair_from(pw, pl):
    """American odds where a bet with win prob pw and loss prob pl breaks even."""
    if pw <= 0.0005:
        return None
    return dec_am(1 + pl / pw)


def ev_of(pw, pl, am):
    return pw * (am_dec(am) - 1) - pl


def novig(a, b):
    if a is None or b is None:
        return None, None
    x, y = 1 / am_dec(a), 1 / am_dec(b)
    return x / (x + y), y / (x + y)


def ncdf(x):
    return 0.5 * (1 + math.erf(x / math.sqrt(2)))


def line_probs(mu, sd, line):
    """P(X > line), P(X == line), P(X < line) for an integer-valued score difference or total."""
    if abs(line - round(line)) < 1e-9:
        hi = 1 - ncdf((line + 0.5 - mu) / sd)
        lo = ncdf((line - 0.5 - mu) / sd)
        return hi, max(0.0, 1 - hi - lo), lo
    hi = 1 - ncdf((line - mu) / sd)
    return hi, 0.0, 1 - hi


def nb_params(mu, var):
    """Negative binomial (r, p) for mean mu and variance var; Poisson when var <= mu."""
    mu = max(mu, 1e-6)
    if var <= mu * 1.0001:
        return None, None
    p = mu / var
    r = mu * p / (1 - p)
    return r, p


def count_cdf_table(mu, var, kmax):
    """P(X <= k) for k = 0..kmax under NB(mu, var) (Poisson if not over-dispersed)."""
    r, p = nb_params(mu, var)
    out, c = [], 0.0
    if r is None:
        pk = math.exp(-mu)
        for k in range(kmax + 1):
            c += pk
            out.append(min(c, 1.0))
            pk *= mu / (k + 1)
    else:
        pk = p ** r
        for k in range(kmax + 1):
            c += pk
            out.append(min(c, 1.0))
            pk *= (k + r) / (k + 1) * (1 - p)
    return out


def p_over_count(mu, var, line):
    k = int(math.floor(line))
    if k < 0:
        return 1.0
    return 1 - count_cdf_table(mu, var, k)[k]


# --------------------------------------------------------------------------
# Data: sportsdataverse releases (box scores) + ESPN (schedule, odds, injuries)
# --------------------------------------------------------------------------
PLAYER_COLS = ["game_id", "season", "season_type", "game_date", "athlete_id", "athlete_display_name",
               "athlete_short_name", "athlete_position_abbreviation", "team_id", "minutes",
               "field_goals_made", "field_goals_attempted", "three_point_field_goals_made",
               "three_point_field_goals_attempted", "free_throws_made", "free_throws_attempted",
               "offensive_rebounds", "defensive_rebounds", "rebounds", "assists", "steals", "blocks",
               "turnovers", "fouls", "plus_minus", "points", "starter", "did_not_play", "reason"]
TEAM_COLS = ["game_id", "team_id", "team_abbreviation", "team_display_name", "team_short_display_name",
             "team_color", "team_logo", "team_score", "field_goals_made", "field_goals_attempted",
             "three_point_field_goals_made", "three_point_field_goals_attempted", "free_throws_made",
             "free_throws_attempted", "offensive_rebounds", "defensive_rebounds", "total_rebounds",
             "assists", "steals", "blocks", "turnovers", "total_turnovers", "fouls",
             "points_in_paint", "fast_break_points"]
SCHED_COLS = ["game_id", "season", "season_type", "type_abbreviation", "date", "game_date", "neutral_site",
              "status_type_completed", "status_period", "home_id", "away_id", "home_abbreviation",
              "away_abbreviation", "home_score", "away_score", "home_linescores", "away_linescores",
              "venue_full_name", "home_conference_id", "away_conference_id", "home_current_rank",
              "away_current_rank", "home_display_name", "away_display_name", "home_short_display_name",
              "away_short_display_name", "home_logo", "away_logo", "home_color", "away_color",
              "conference_competition", "notes_headline", "date"]


def _read_parquet(path, cols):
    t = pq.read_table(path)
    have = [c for c in cols if c in t.column_names]
    return t.select(have).to_pylist()


def load_release(api, kind, season, current):
    url = f"{REL}/{REL_FILES[kind].format(s=season)}"
    path = os.path.join(DIRS["release"], os.path.basename(url))
    max_age = 4 * 3600 if current else None
    b = api.get_bytes(url, path, max_age=max_age, tries=3, timeout=120)
    if b is None or not os.path.exists(path):
        return []
    cols = {"player": PLAYER_COLS, "team": TEAM_COLS, "sched": SCHED_COLS}[kind]
    try:
        return _read_parquet(path, cols)
    except Exception as e:  # corrupt download
        log(f"    ! could not read {os.path.basename(path)}: {e}")
        try:
            os.remove(path)
        except OSError:
            pass
        return []


class DB:
    """Everything known about completed games and teams."""

    def __init__(self):
        self.games = {}     # gid -> game dict
        self.tbox = {}      # (gid, tid) -> team box
        self.pbox = []      # player rows
        self.teams = {}     # tid -> meta
        self.lines = {}     # gid -> closing line dict
        self.pnames = {}    # pid -> name info
        self.conf = {}      # tid -> ESPN conference id (Division I teams only)
        self.rank = {}      # tid -> latest AP rank seen
        self.sched_upcoming = []

    def is_d1(self, tid):
        return tid in self.conf

    def mid(self, tid):
        """Team id used by the model: non-Division I teams share one rating."""
        return tid if tid in self.conf else NOND1

    def team_by_abbr(self, ab):
        for t, m in self.teams.items():
            if m["abbr"] == ab:
                return t
        return None


def _ls(v):
    out = {}
    if isinstance(v, str):  # the release stores these as text: "[{'displayValue': '25', 'period': 1, ...}\n ...]"
        for blk in re.findall(r"\{[^{}]*\}", v):
            mp, mv = re.search(r"'period':\s*(\d+)", blk), re.search(r"'value':\s*([-\d.]+)", blk)
            if mp and mv:
                out[int(mp.group(1))] = float(mv.group(1))
        return out
    for x in (v or []):
        try:
            out[int(x.get("period"))] = float(x.get("value"))
        except (TypeError, ValueError, AttributeError):
            pass
    return out


def note_teams(db, r):
    """Conference, rank and display info for both teams of a schedule row (latest season wins)."""
    for side in ("home", "away"):
        try:
            tid = int(r[f"{side}_id"])
        except (TypeError, ValueError, KeyError):
            continue
        cid = r.get(f"{side}_conference_id")
        if cid is not None and not (isinstance(cid, float) and math.isnan(cid)):
            db.conf[tid] = int(cid)
        rk = r.get(f"{side}_current_rank")
        if rk is not None and not (isinstance(rk, float) and math.isnan(rk)) and 1 <= int(rk) <= 25:
            db.rank[tid] = int(rk)
        else:
            db.rank.pop(tid, None)   # rows are in date order, so the latest poll wins
        if r.get(f"{side}_abbreviation"):
            m = db.teams.setdefault(tid, {"id": tid})
            m.update({"abbr": r[f"{side}_abbreviation"], "name": r.get(f"{side}_display_name") or m.get("name", ""),
                      "short": r.get(f"{side}_short_display_name") or m.get("short", ""),
                      "color": r.get(f"{side}_color") or m.get("color", "555555"),
                      "logo": r.get(f"{side}_logo") or m.get("logo", "")})


def add_release(db, sched, tbox, pbox):
    valid = set()
    for r in sorted(sched, key=lambda x: str(x.get("game_date"))):
        note_teams(db, r)
    for r in sched:
        if not r.get("status_type_completed"):
            continue
        if r.get("season_type") not in (2, 3):
            continue
        try:
            h, a = int(r["home_id"]), int(r["away_id"])
        except (TypeError, ValueError):
            continue
        if r.get("home_score") is None or r.get("away_score") is None:
            continue
        gid = str(r["game_id"])
        per = int(r.get("status_period") or 2)
        hl, al = _ls(r.get("home_linescores")), _ls(r.get("away_linescores"))
        db.games[gid] = {
            "gid": gid, "date": str(r["game_date"])[:10], "season": int(r["season"]),
            "stype": int(r["season_type"]), "home": h, "away": a,
            "hs": int(r.get("home_score") or 0), "as": int(r.get("away_score") or 0),
            "periods": max(2, per), "neutral": bool(r.get("neutral_site")),
            "hq": [hl.get(1)], "aq": [al.get(1)],
            "venue": r.get("venue_full_name") or "", "conf_game": bool(r.get("conference_competition")),
        }
        valid.add(gid)
    for r in tbox:
        gid = str(r["game_id"])
        if gid not in valid:
            continue
        tid = int(r["team_id"])
        tov = r.get("total_turnovers")
        if tov is None:
            tov = r.get("turnovers")
        db.tbox[(gid, tid)] = {
            "pts": fnum(r.get("team_score"), 0), "fgm": fnum(r.get("field_goals_made"), 0),
            "fga": fnum(r.get("field_goals_attempted"), 0), "fg3m": fnum(r.get("three_point_field_goals_made"), 0),
            "fg3a": fnum(r.get("three_point_field_goals_attempted"), 0), "ftm": fnum(r.get("free_throws_made"), 0),
            "fta": fnum(r.get("free_throws_attempted"), 0), "oreb": fnum(r.get("offensive_rebounds"), 0),
            "dreb": fnum(r.get("defensive_rebounds"), 0), "reb": fnum(r.get("total_rebounds"), 0),
            "ast": fnum(r.get("assists"), 0), "stl": fnum(r.get("steals"), 0), "blk": fnum(r.get("blocks"), 0),
            "tov": fnum(tov, 0), "pf": fnum(r.get("fouls"), 0),
            "paint": fnum(r.get("points_in_paint"), 0), "fb": fnum(r.get("fast_break_points"), 0),
        }
        if r.get("team_abbreviation") and "abbr" not in db.teams.get(tid, {}):
            db.teams[tid] = {"id": tid, "abbr": r["team_abbreviation"], "name": r.get("team_display_name") or "",
                             "short": r.get("team_short_display_name") or "", "color": r.get("team_color") or "555555",
                             "logo": r.get("team_logo") or ""}
    for r in pbox:
        gid = str(r["game_id"])
        if gid not in valid:
            continue
        db.pbox.append(_prow(gid, db.games[gid], r))


def _prow(gid, g, r):
    mn = fnum(r.get("minutes"), 0.0) or 0.0
    return {
        "gid": gid, "date": g["date"], "season": g["season"], "stype": g["stype"],
        "tid": int(r["team_id"]), "pid": str(r["athlete_id"]),
        "name": r.get("athlete_display_name") or "", "short": r.get("athlete_short_name") or "",
        "pos": r.get("athlete_position_abbreviation") or "",
        "min": mn, "pts": fnum(r.get("points"), 0), "reb": fnum(r.get("rebounds"), 0),
        "ast": fnum(r.get("assists"), 0), "fg3m": fnum(r.get("three_point_field_goals_made"), 0),
        "fg3a": fnum(r.get("three_point_field_goals_attempted"), 0),
        "fgm": fnum(r.get("field_goals_made"), 0), "fga": fnum(r.get("field_goals_attempted"), 0),
        "ftm": fnum(r.get("free_throws_made"), 0), "fta": fnum(r.get("free_throws_attempted"), 0),
        "oreb": fnum(r.get("offensive_rebounds"), 0), "dreb": fnum(r.get("defensive_rebounds"), 0),
        "stl": fnum(r.get("steals"), 0), "blk": fnum(r.get("blocks"), 0), "tov": fnum(r.get("turnovers"), 0),
        "pf": fnum(r.get("fouls"), 0), "pm": fnum(r.get("plus_minus"), 0),
        "starter": bool(r.get("starter")), "dnp": bool(r.get("did_not_play")) or mn <= 0,
        "reason": txt(r.get("reason")),
    }


# ---- ESPN scoreboard ----
def _pick(d):
    if not isinstance(d, dict):
        return None, None
    for k in ("close", "current", "open"):
        x = d.get(k)
        if isinstance(x, dict) and (x.get("odds") is not None or x.get("american") is not None):
            return parse_line(x.get("line")), parse_am(x.get("odds", x.get("american")))
    return None, None


def parse_espn_odds(olist, home_id=None):
    """Moneyline / spread / total from an ESPN odds list (scoreboard 'odds' or summary 'pickcenter')."""
    if not olist:
        return None
    o = olist[0]
    res = {"ml": {}, "sp": {}, "tot": None, "src": txt((o.get("provider") or {}).get("name")) or "ESPN",
           "prov": txt((o.get("provider") or {}).get("id"))}
    for side, k in (("H", "home"), ("A", "away")):
        _, v = _pick((o.get("moneyline") or {}).get(k))
        if v is not None:
            res["ml"][side] = v
        ln, v = _pick((o.get("pointSpread") or {}).get(k))
        if ln is not None and v is not None:
            res["sp"][side] = (ln, v)
    lo_, vo = _pick((o.get("total") or {}).get("over"))
    lu_, vu = _pick((o.get("total") or {}).get("under"))
    if lo_ is not None and vo is not None and vu is not None:
        res["tot"] = (lo_, vo, vu)
    # older flat layout
    for side, k in (("H", "homeTeamOdds"), ("A", "awayTeamOdds")):
        to = o.get(k) or {}
        if side not in res["ml"] and parse_am(to.get("moneyLine")) is not None:
            res["ml"][side] = parse_am(to.get("moneyLine"))
    if len(res["sp"]) < 2 and o.get("spread") is not None:
        s = parse_line(o.get("spread"))
        ho, ao = o.get("homeTeamOdds") or {}, o.get("awayTeamOdds") or {}
        if s is not None:
            hs = s
            if ho.get("favorite") is True:
                hs = -abs(s)
            elif ao.get("favorite") is True:
                hs = abs(s)
            hsp, asp = parse_am(ho.get("spreadOdds")) or -110, parse_am(ao.get("spreadOdds")) or -110
            res["sp"] = {"H": (hs, hsp), "A": (-hs, asp)}
    if res["tot"] is None and o.get("overUnder") is not None:
        vo, vu = parse_am(o.get("overOdds")) or -110, parse_am(o.get("underOdds")) or -110
        res["tot"] = (float(o["overUnder"]), vo, vu)
    if len(res["sp"]) == 2 and abs(res["sp"]["H"][0] + res["sp"]["A"][0]) > 1e-6:
        res["sp"] = {}
    return res if (res["ml"] or res["sp"] or res["tot"]) else None


def parse_scoreboard(js):
    out = []
    for e in (js or {}).get("events", []):
        try:
            c = e["competitions"][0]
            comps = {x["homeAway"]: x for x in c["competitors"]}
            h, a = comps["home"], comps["away"]
            hid, aid = int(h["team"]["id"]), int(a["team"]["id"])
        except (KeyError, IndexError, TypeError, ValueError):
            continue
        utc = parse_utc(e.get("date"))
        st = (e.get("status") or c.get("status") or {}).get("type") or {}

        def rank(x):
            r = (x.get("curatedRank") or {}).get("current")
            return int(r) if isinstance(r, (int, float)) and 1 <= r <= 25 else None

        def confid(x):
            v = (x.get("team") or {}).get("conferenceId")
            try:
                return int(v) if v not in (None, "") else None
            except (TypeError, ValueError):
                return None

        def rec(x, kind):
            for r in x.get("records") or []:
                if r.get("type") == kind or r.get("name", "").lower() == kind:
                    return r.get("summary")
            return None

        bc = []
        for b in c.get("broadcasts") or []:
            bc += b.get("names") or []
        out.append({
            "gid": str(e["id"]), "utc": utc, "date": (to_et(utc).date().isoformat() if utc else None),
            "state": st.get("state") or "pre", "completed": bool(st.get("completed")),
            "detail": st.get("shortDetail") or "", "home": hid, "away": aid,
            "habbr": h["team"].get("abbreviation"), "aabbr": a["team"].get("abbreviation"),
            "hs": fnum(h.get("score")), "as": fnum(a.get("score")),
            "hrec": rec(h, "total"), "arec": rec(a, "total"),
            "neutral": bool(c.get("neutralSite")), "venue": ((c.get("venue") or {}).get("fullName") or ""),
            "tv": ", ".join(dict.fromkeys(bc)),
            "odds": parse_espn_odds(c.get("odds") or []),
            "stype": ((e.get("season") or {}).get("type")),
            "note": "; ".join(n.get("headline", "") for n in (c.get("notes") or []) if n.get("headline")),
            "hrank": rank(h), "arank": rank(a), "hconf": confid(h), "aconf": confid(a),
            "conf_game": bool(c.get("conferenceCompetition")),
            "hname": h["team"].get("displayName"), "aname": a["team"].get("displayName"),
            "hshort": h["team"].get("shortDisplayName"), "ashort": a["team"].get("shortDisplayName"),
            "hlogo": h["team"].get("logo"), "alogo": a["team"].get("logo"),
            "hcolor": h["team"].get("color"), "acolor": a["team"].get("color"),
        })
    return out


def fetch_scoreboard(api, d, live_window):
    ds = d.strftime("%Y%m%d")
    path = os.path.join(DIRS["sb"], f"sb_{ds}.json")
    max_age = 600 if live_window else None
    if not live_window and os.path.exists(path):
        js = jload(path)
        # a cached past date that still has unfinished games gets refreshed
        if js and any(not x["completed"] for x in parse_scoreboard(js)):
            max_age = 600
    # groups=50 is all of Division I (without it ESPN returns only featured games)
    js = api.get(f"{ESPN_SITE}/scoreboard?dates={ds}&groups=50&limit=500", path, max_age=max_age)
    return parse_scoreboard(js)


# ---- ESPN summary -> box rows (for games newer than the data release) ----
def summary_to_rows(js):
    try:
        hc = js["header"]["competitions"][0]
        comps = {x["homeAway"]: x for x in hc["competitors"]}
        h, a = comps["home"], comps["away"]
        gid = str(js["header"]["id"])
        utc = parse_utc(hc.get("date"))
        stt = (hc.get("status") or {}).get("type") or {}
        if not stt.get("completed"):
            return None
        per = int((hc.get("status") or {}).get("period") or 2)
        season = int((js["header"].get("season") or {}).get("year") or season_for(to_et(utc).date()))
        stype = int((js["header"].get("season") or {}).get("type") or 2)
    except (KeyError, IndexError, TypeError, ValueError):
        return None
    hl = {int(x.get("period", i + 1)): fnum(x.get("value", x.get("displayValue"))) for i, x in enumerate(h.get("linescores") or [])}
    al = {int(x.get("period", i + 1)): fnum(x.get("value", x.get("displayValue"))) for i, x in enumerate(a.get("linescores") or [])}
    g = {"gid": gid, "date": to_et(utc).date().isoformat(), "season": season, "stype": stype,
         "home": int(h["id"]), "away": int(a["id"]), "hs": int(fnum(h.get("score"), 0)),
         "as": int(fnum(a.get("score"), 0)), "periods": max(2, per), "neutral": bool(hc.get("neutralSite")),
         "hq": [hl.get(1)], "aq": [al.get(1)], "venue": "", "conf_game": bool(hc.get("conferenceCompetition"))}
    tb = {}
    for t in (js.get("boxscore") or {}).get("teams") or []:
        tid = int(t["team"]["id"])
        st = {x.get("name"): x.get("displayValue") for x in t.get("statistics") or []}

        def mk(k):
            v = st.get(k) or "0-0"
            p = str(v).split("-")
            return (fnum(p[0], 0), fnum(p[1], 0)) if len(p) == 2 else (0, 0)
        fgm, fga = mk("fieldGoalsMade-fieldGoalsAttempted")
        f3m, f3a = mk("threePointFieldGoalsMade-threePointFieldGoalsAttempted")
        ftm, fta = mk("freeThrowsMade-freeThrowsAttempted")
        tb[tid] = {"pts": g["hs"] if tid == g["home"] else g["as"], "fgm": fgm, "fga": fga, "fg3m": f3m,
                   "fg3a": f3a, "ftm": ftm, "fta": fta, "oreb": fnum(st.get("offensiveRebounds"), 0),
                   "dreb": fnum(st.get("defensiveRebounds"), 0), "reb": fnum(st.get("totalRebounds"), 0),
                   "ast": fnum(st.get("assists"), 0), "stl": fnum(st.get("steals"), 0),
                   "blk": fnum(st.get("blocks"), 0),
                   "tov": fnum(st.get("totalTurnovers", st.get("turnovers")), 0), "pf": fnum(st.get("fouls"), 0),
                   "paint": fnum(st.get("pointsInPaint"), 0), "fb": fnum(st.get("fastBreakPoints"), 0)}
    prows = []
    for p in (js.get("boxscore") or {}).get("players") or []:
        tid = int(p["team"]["id"])
        for s in p.get("statistics") or []:
            keys = s.get("keys") or []
            for at in s.get("athletes") or []:
                a_ = at.get("athlete") or {}
                vals = dict(zip(keys, at.get("stats") or []))

                def pair(k):
                    v = str(vals.get(k) or "0-0").split("-")
                    return (fnum(v[0], 0), fnum(v[1], 0)) if len(v) == 2 else (0, 0)
                fgm, fga = pair("fieldGoalsMade-fieldGoalsAttempted")
                f3m, f3a = pair("threePointFieldGoalsMade-threePointFieldGoalsAttempted")
                ftm, fta = pair("freeThrowsMade-freeThrowsAttempted")
                r = {"game_id": gid, "team_id": tid, "athlete_id": a_.get("id"),
                     "athlete_display_name": a_.get("displayName"), "athlete_short_name": a_.get("shortName"),
                     "athlete_position_abbreviation": (a_.get("position") or {}).get("abbreviation"),
                     "minutes": vals.get("minutes"), "points": vals.get("points"), "rebounds": vals.get("rebounds"),
                     "assists": vals.get("assists"), "three_point_field_goals_made": f3m,
                     "three_point_field_goals_attempted": f3a, "field_goals_made": fgm,
                     "field_goals_attempted": fga, "free_throws_made": ftm, "free_throws_attempted": fta,
                     "offensive_rebounds": vals.get("offensiveRebounds"),
                     "defensive_rebounds": vals.get("defensiveRebounds"), "steals": vals.get("steals"),
                     "blocks": vals.get("blocks"), "turnovers": vals.get("turnovers"), "fouls": vals.get("fouls"),
                     "plus_minus": vals.get("plusMinus"), "starter": at.get("starter"),
                     "did_not_play": at.get("didNotPlay") or not at.get("stats"), "reason": at.get("reason")}
                if r["athlete_id"]:
                    prows.append(_prow(gid, g, r))
    meta = {}
    for side in (h, a):
        t = side.get("team") or {}
        try:
            tid = int(t.get("id") or side.get("id"))
        except (TypeError, ValueError):
            continue
        logo = t.get("logo") or ((t.get("logos") or [{}])[0].get("href"))
        meta[tid] = {"id": tid, "abbr": t.get("abbreviation"), "name": t.get("displayName") or "",
                     "short": t.get("shortDisplayName") or t.get("name") or "", "color": t.get("color") or "555555",
                     "logo": logo or ""}
    lines = parse_espn_odds(js.get("pickcenter") or [])
    return {"game": g, "tbox": tb, "pbox": prows, "meta": meta, "lines": lines}


def fetch_summary_compact(api, gid):
    path = os.path.join(DIRS["games"], f"{gid}.json")
    c = jload(path)
    if c:
        return c
    js = api.get(f"{ESPN_SITE}/summary?event={gid}", None, tries=2)
    if not js:
        return None
    c = summary_to_rows(js)
    if c:
        jdump(c, path)
    return c


# ---- injuries / rosters / props ----
def fetch_injuries(api):
    js = api.get(f"{ESPN_SITE}/injuries", os.path.join(DIRS["misc"], "injuries.json"), max_age=900)
    out = {}
    for t in (js or {}).get("injuries", []):
        for x in t.get("injuries") or []:
            a = x.get("athlete") or {}
            pid = a.get("id")
            if not pid:
                m = re.search(r"/id/(\d+)", json.dumps(a.get("links") or []))
                pid = m.group(1) if m else None
            try:
                tid = int(((a.get("team") or {}).get("id")) or t.get("id"))
            except (TypeError, ValueError):
                tid = None
            det = x.get("details") or {}
            parts = [det.get("type"), det.get("detail")]
            out[str(pid or a.get("displayName"))] = {
                "pid": str(pid) if pid else None, "name": a.get("displayName") or "", "tid": tid,
                "status": x.get("status") or (x.get("type") or {}).get("description") or "",
                "detail": " – ".join(p for p in parts if p and p != "Not Specified"),
                "ret": det.get("returnDate") or "", "date": (x.get("date") or "")[:10],
                "note": x.get("shortComment") or "",
            }
    return out


def fetch_rosters(api, team_ids):
    def one(tid):
        js = api.get(f"{ESPN_SITE}/teams/{tid}/roster", os.path.join(DIRS["misc"], f"roster_{tid}.json"),
                     max_age=6 * 3600, tries=2)
        if not js:
            return tid, None
        ath = js.get("athletes") or []
        if ath and isinstance(ath[0], dict) and "items" in ath[0]:  # grouped layout
            ath = [i for grp in ath for i in grp.get("items") or []]
        return tid, {str(a.get("id")): a.get("displayName") for a in ath if a.get("id")}
    with ThreadPoolExecutor(CONFIG["workers"]) as ex:
        res = dict(ex.map(one, team_ids))
    return {k: v for k, v in res.items() if v}


PROP_TYPES = [  # (regex on ESPN prop name, our stat key)
    (r"points.*rebounds.*assists|pts.*reb.*ast|\bpra\b", "pra"),
    (r"points.*rebounds|pts.*reb", "pr"),
    (r"points.*assists|pts.*ast", "pa"),
    (r"rebounds.*assists|reb.*ast", "ra"),
    (r"three|3-?pt|3pm", "fg3m"),
    (r"rebound", "reb"),
    (r"assist", "ast"),
    (r"point", "pts"),
]


def _walk(o):
    if isinstance(o, dict):
        yield o
        for v in o.values():
            yield from _walk(v)
    elif isinstance(o, list):
        for v in o:
            yield from _walk(v)


def parse_propbets(js):
    """Best-effort parse of ESPN's propBets feed into {(pid, stat): (line, over, under)}."""
    out = {}
    for it in (js or {}).get("items", []):
        name = txt((it.get("type") or {}).get("name") or it.get("name") or (it.get("type") or {}).get("displayName")).lower()
        if any(w in name for w in ("double", "first", "triple", "quarter", "half", "1st")):
            continue
        stat = None
        for rx, k in PROP_TYPES:
            if re.search(rx, name):
                stat = k
                break
        if not stat:
            continue
        ref = json.dumps(it.get("athlete") or {})
        m = re.search(r"athletes/(\d+)", ref)
        if not m:
            continue
        pid = m.group(1)
        line, over, under = None, None, None
        for d in _walk(it):
            for lk in ("target", "total", "line"):
                v = d.get(lk)
                if line is None and v is not None:
                    line = parse_line(v.get("value") if isinstance(v, dict) else v)
            for k, v in d.items():
                kl = str(k).lower()
                if kl == "over" and over is None:
                    over = parse_am(v.get("american") if isinstance(v, dict) else v)
                if kl == "under" and under is None:
                    under = parse_am(v.get("american") if isinstance(v, dict) else v)
        if line is None or (over is None and under is None):
            continue
        if line < 0.4 or abs(line * 2 - round(line * 2)) > 1e-6:
            continue
        key = (pid, stat)
        if key not in out:
            out[key] = (line, over, under)
    return out


def fetch_props(api, gid, prov):
    if not prov:
        return {}
    js = api.get(f"{ESPN_CORE}/events/{gid}/competitions/{gid}/odds/{prov}/propBets?limit=1000",
                 os.path.join(DIRS["misc"], f"props_{gid}.json"), max_age=1800, tries=1)
    try:
        return parse_propbets(js)
    except Exception:
        return {}


def load_data(api, today):
    """Completed games for last season and this season, plus closing lines."""
    cur = season_for(today)
    db = DB()
    if pq is None:
        log("  ! pyarrow is not installed: run  pip install pyarrow  (needed to read the box score files)")
    db.sched_upcoming = []
    for season in (cur - 1, cur):
        log(f"  Box scores {season - 1}-{str(season)[2:]} ...")
        sched = load_release(api, "sched", season, season == cur) if pq else []
        tb = load_release(api, "team", season, season == cur) if pq else []
        pb = load_release(api, "player", season, season == cur) if pq else []
        add_release(db, sched, tb, pb)
        if season == cur:
            db.sched_upcoming = [r for r in sched if not r.get("status_type_completed")]
    # season start = first game of the current season in the schedule, else Oct 15
    cur_dates = sorted(g["date"] for g in db.games.values() if g["season"] == cur)
    start = ddate(cur_dates[0]) if cur_dates else dt.date(today.year if today.month >= 8 else today.year - 1, 10, 15)
    if today < start:
        start = today
    # walk this season's dates on ESPN: finds games newer than the release and closing lines
    dates = [start + dt.timedelta(days=i) for i in range((today - start).days + 1)]
    log(f"  ESPN scoreboards for {len(dates)} dates this season ...")
    with ThreadPoolExecutor(CONFIG["workers"]) as ex:
        boards = list(ex.map(lambda d: fetch_scoreboard(api, d, d >= today - dt.timedelta(days=1)), dates))
    missing = []
    lines_path = os.path.join(DIRS["root"], "closing_lines.json")
    db.lines = jload(lines_path, {}) or {}
    need_lines = []
    for evs in boards:
        for e in evs:
            note_scoreboard_teams(db, e)
            if not e["completed"] or e.get("stype") not in (None, 2, 3):
                continue
            if e["gid"] not in db.games:
                missing.append(e["gid"])
            if e["odds"] and e["gid"] not in db.lines:
                db.lines[e["gid"]] = _line_rec(e["odds"])
            elif e["gid"] not in db.lines and e["home"] in db.conf and e["away"] in db.conf:
                need_lines.append((e["date"] or "", e["gid"]))
    # closing lines for past games come from game summaries; take the newest few hundred per run
    # (the cache keeps them, so the season's ATS records fill in over a few runs)
    need_lines = [g for d, g in sorted(need_lines, reverse=True)[:CONFIG.get("max_line_fetch", 250)]]
    todo = sorted(set(missing) | set(need_lines))
    if todo:
        log(f"  Game summaries for {len(todo)} games ({len(missing)} not yet in the box score files) ...")
        with ThreadPoolExecutor(CONFIG["workers"]) as ex:
            comps = list(ex.map(lambda g: fetch_summary_compact(api, g), todo))
        for gid, c in zip(todo, comps):
            if not c:
                continue
            if c.get("lines") and gid not in db.lines:
                db.lines[gid] = _line_rec(c["lines"])
            if gid in db.games:
                continue
            g = c["game"]
            db.games[gid] = g
            for tid, b in c["tbox"].items():
                db.tbox[(gid, int(tid))] = b
            db.pbox += c["pbox"]
            for tid, m in c["meta"].items():
                db.teams.setdefault(int(tid), m)
    jdump(db.lines, lines_path)
    for r in db.pbox:
        db.pnames[r["pid"]] = (r["name"], r["short"], r["pos"])
    db.pbox.sort(key=lambda r: (r["date"], r["gid"]))
    return db, boards


def note_scoreboard_teams(db, e):
    for side, tid in (("h", e["home"]), ("a", e["away"])):
        if e.get(side + "conf") is not None:
            db.conf[tid] = e[side + "conf"]
        if e.get("state") == "pre":
            if e.get(side + "rank"):
                db.rank[tid] = e[side + "rank"]
            else:
                db.rank.pop(tid, None)
        m = db.teams.setdefault(tid, {"id": tid, "color": "555555", "logo": ""})
        for k, src in (("abbr", side + "abbr"), ("name", side + "name"), ("short", side + "short"),
                       ("logo", side + "logo"), ("color", side + "color")):
            v = e.get(src) if src != side + "abbr" else e.get("habbr" if side == "h" else "aabbr")
            if v:
                m[k] = v


def _line_rec(o):
    rec = {"src": o.get("src")}
    if o.get("sp") and "H" in o["sp"]:
        rec["sp"] = o["sp"]["H"][0]
    if o.get("tot"):
        rec["tot"] = o["tot"][0]
    if o.get("ml"):
        rec["mlh"], rec["mla"] = o["ml"].get("H"), o["ml"].get("A")
    return rec


# --------------------------------------------------------------------------
# Team model
# --------------------------------------------------------------------------
def poss_of(b):
    return b["fga"] - b["oreb"] + b["tov"] + 0.44 * b["fta"]


def game_records(db, seasons=None):
    """One record per completed game with possessions, pace (per 40 minutes) and efficiency."""
    recs = []
    for gid, g in db.games.items():
        if seasons and g["season"] not in seasons:
            continue
        if g["home"] not in db.conf and g["away"] not in db.conf:
            continue
        th, ta = db.tbox.get((gid, g["home"])), db.tbox.get((gid, g["away"]))
        if not th or not ta:
            continue
        poss = (poss_of(th) + poss_of(ta)) / 2
        if poss < 45:
            continue
        mins = 40 + 5 * (g["periods"] - 2)
        recs.append({**g, "poss": poss, "pace": poss * 40 / mins, "mins": mins, "th": th, "ta": ta,
                     "mh": db.mid(g["home"]), "ma": db.mid(g["away"])})
    recs.sort(key=lambda r: (r["date"], r["gid"]))
    return recs


def team_dates(db, extra=()):
    """team id -> sorted list of game dates (completed + scheduled)."""
    td = {}
    for g in db.games.values():
        for t in (g["home"], g["away"]):
            td.setdefault(t, set()).add(g["date"])
    for d, h, a in extra:
        td.setdefault(h, set()).add(d)
        td.setdefault(a, set()).add(d)
    return {t: sorted(v) for t, v in td.items()}


def rest_days(tdates, tid, date):
    """Days since this team's previous game, None if no earlier game in data."""
    ds = tdates.get(tid) or []
    prev = [d for d in ds if d < date]
    if not prev:
        return None
    return (ddate(date) - ddate(prev[-1])).days


def _ridge(n, rows_idx, rows_val, y, w, prior, lam):
    """Weighted ridge regression toward `prior`, built from sparse rows (few nonzeros each)."""
    A = np.zeros((n, n))
    bvec = np.zeros(n)
    k = rows_idx.shape[1]
    for i in range(k):
        for j in range(k):
            np.add.at(A, (rows_idx[:, i], rows_idx[:, j]), w * rows_val[:, i] * rows_val[:, j])
        np.add.at(bvec, rows_idx[:, i], w * rows_val[:, i] * y)
    A[np.diag_indices(n)] += lam
    bvec += lam * prior
    return np.linalg.solve(A, bvec)


def fit_team_model(recs, asof, prior=None, hl_days=None, lam=None, teams=None):
    """Opponent-adjusted offence, defence (points per 100 possessions) and pace (possessions per 40).

    eff(team offence) = mu + o[team] - d[opp] + hca * home(+-0.5, 0 on neutral floors)
    pace(game)        = mu_p + p[home] + p[away]
    Each team's ratings are pulled toward `prior` with the weight of `lam` games.
    """
    hl = hl_days or CONFIG["hl_days"]
    lam = CONFIG["prior_games"] if lam is None else lam
    prior = prior or {}
    asof_d = ddate(asof)
    use = [r for r in recs if r["date"] < asof]
    tset = set(teams or ()) | {r["mh"] for r in use} | {r["ma"] for r in use} | set(prior.get("o", {})) | {NOND1}
    tl = sorted(tset)
    ix = {t: i for i, t in enumerate(tl)}
    T = len(tl)
    P = 2 + 2 * T
    n = len(use)
    m = {"teams": tl, "lam": lam, "hl": hl}
    if n:
        w = np.array([0.5 ** ((asof_d - ddate(r["date"])).days / hl) for r in use])
        hc = np.array([0.0 if r["neutral"] else 0.5 for r in use])
        th = np.array([ix[r["mh"]] for r in use])
        ta = np.array([ix[r["ma"]] for r in use])
        poss = np.array([r["poss"] for r in use])
        eh = 100 * np.array([r["hs"] for r in use]) / poss
        ea = 100 * np.array([r["as"] for r in use]) / poss
        # rows: [mu, hca, o[team], d[opp]]
        ridx = np.vstack([np.column_stack([np.zeros(n, int), np.ones(n, int), 2 + th, 2 + T + ta]),
                          np.column_stack([np.zeros(n, int), np.ones(n, int), 2 + ta, 2 + T + th])])
        rval = np.vstack([np.column_stack([np.ones(n), hc, np.ones(n), -np.ones(n)]),
                          np.column_stack([np.ones(n), -hc, np.ones(n), -np.ones(n)])])
        y = np.concatenate([eh, ea])
        ww = np.concatenate([w, w])
    else:
        ridx = np.zeros((0, 4), int)
        rval = np.zeros((0, 4))
        y = ww = np.zeros(0)
    pr = np.zeros(P)
    lv = np.full(P, float(lam))
    pr[0], lv[0] = prior.get("mu", 102.0), 0.05
    pr[1], lv[1] = prior.get("hca", CONFIG["hca"]), 400.0
    for t in tl:
        pr[2 + ix[t]] = prior.get("o", {}).get(t, prior.get("o_new", -2.0))
        pr[2 + T + ix[t]] = prior.get("d", {}).get(t, prior.get("d_new", -2.0))
    if NOND1 in ix:  # the pooled non-D1 rating is weakly held: plenty of games every November
        lv[2 + ix[NOND1]] = lv[2 + T + ix[NOND1]] = 3.0
        if NOND1 not in prior.get("o", {}):
            half = CONFIG["nond1_rating"] * 100 / 68 / 2
            pr[2 + ix[NOND1]] = pr[2 + T + ix[NOND1]] = half
    beta = _ridge(P, ridx, rval, y, ww, pr, lv)
    m.update({"mu": float(beta[0]), "hca": float(beta[1]),
              "o": {t: float(beta[2 + ix[t]]) for t in tl}, "d": {t: float(beta[2 + T + ix[t]]) for t in tl}})
    # pace
    Pp = 1 + T
    if n:
        pidx = np.column_stack([np.zeros(n, int), 1 + th, 1 + ta])
        pval = np.ones((n, 3))
        py = np.array([r["pace"] for r in use])
        pw = w
    else:
        pidx, pval, py, pw = np.zeros((0, 3), int), np.zeros((0, 3)), np.zeros(0), np.zeros(0)
    ppr = np.zeros(Pp)
    plv = np.full(Pp, float(lam))
    ppr[0], plv[0] = prior.get("mu_p", 68.0), 0.05
    for t in tl:
        ppr[1 + ix[t]] = prior.get("p", {}).get(t, 0.0)
    bp = _ridge(Pp, pidx, pval, py, pw, ppr, plv)
    m.update({"mu_p": float(bp[0]), "p": {t: float(bp[1 + ix[t]]) for t in tl}})
    wt = {}
    for r in use:
        ww_ = 0.5 ** ((asof_d - ddate(r["date"])).days / hl)
        for t in (r["mh"], r["ma"]):
            wt[t] = wt.get(t, 0.0) + ww_
    m["wt"] = wt
    m["o_new"], m["d_new"] = prior.get("o_new", -2.0), prior.get("d_new", -2.0)
    return m


def rating(m, t, k):
    return m[k].get(t, m.get(k + "_new", 0.0) if k in ("o", "d") else 0.0)


def predict_game(m, h, a, neutral=False, h_b2b=False, a_b2b=False, adj_h=0.0, adj_a=0.0):
    """Expected points (incl. overtime) for home/away. h/a are model team ids (db.mid).
    adj_* = margin points lost to absences (positive = weaker)."""
    hc = 0.0 if neutral else 0.5
    pace = m["mu_p"] + rating(m, h, "p") + rating(m, a, "p")
    eh = m["mu"] + rating(m, h, "o") - rating(m, a, "d") + m["hca"] * hc
    ea = m["mu"] + rating(m, a, "o") - rating(m, h, "d") - m["hca"] * hc
    ph, pa = pace * eh / 100, pace * ea / 100
    ph += -0.55 * adj_h + 0.45 * adj_a
    pa += -0.55 * adj_a + 0.45 * adj_h
    mu_m = ph - pa
    sd = CONFIG["sd_margin"]
    p_ot = 1.0 * math.exp(-0.5 * (mu_m / sd) ** 2) / (sd * math.sqrt(2 * math.pi))
    ot_pts = p_ot * 1.06 * pace * 5 / 40 * (eh + ea) / 200
    return {"ph": ph + ot_pts, "pa": pa + ot_pts, "pace": pace, "eh": eh, "ea": ea, "p_ot": p_ot}


def last_season_prior(db, cur):
    """Fit all of last season (later games count a little more) to seed this season."""
    recs = game_records(db, {cur - 1})
    if len(recs) < 1000:
        return {}
    asof = (ddate(recs[-1]["date"]) + dt.timedelta(days=1)).isoformat()
    return fit_team_model(recs, asof, prior={}, hl_days=120, lam=1.5)


# --------------------------------------------------------------------------
# Player value (for absences and roster turnover)
# --------------------------------------------------------------------------
def game_score(r):
    return (r["pts"] + 0.4 * r["fgm"] - 0.7 * r["fga"] - 0.4 * (r["fta"] - r["ftm"]) + 0.7 * r["oreb"]
            + 0.3 * r["dreb"] + r["stl"] + 0.7 * r["ast"] + 0.7 * r["blk"] - 0.4 * r["pf"] - r["tov"])


def player_values(rows, asof, cur, hl_days=60, opp_adj=None):
    """pid -> game score per 40 (recency weighted, shrunk toward replacement), minutes, team.

    opp_adj: optional {model team id: margin rating}; production against weak opponents counts for less."""
    acc = {}
    asof_d = ddate(asof)
    R = CONFIG["inj_repl"]
    for r in rows:
        if r["date"] >= asof or r["dnp"] or r["min"] <= 0:
            continue
        age = (asof_d - ddate(r["date"])).days
        w = 0.5 ** (age / hl_days) * (1.0 if r["season"] == cur else 0.6)
        gs = game_score(r)
        if opp_adj is not None and r.get("opp") is not None:
            gs += 0.12 * opp_adj.get(r["opp"], 0.0) * r["min"] / 40
        a = acc.setdefault(r["pid"], [0.0, 0.0, 0.0, 0, None, None])
        a[0] += w * gs
        a[1] += w * r["min"]
        a[2] += w
        a[3] += 1
        a[4] = r["tid"]
        a[5] = r["season"]
    out = {}
    for pid, (gs, mn, ww, n, tid, sea) in acc.items():
        shrink = 200.0
        f = min(1.0, ww / max(n, 1))
        gs40 = 40 * (gs + R / 40 * shrink * f) / (mn + shrink * f)
        out[pid] = {"gs40": gs40, "mpg": mn / ww if ww else 0.0, "tid": tid, "last_season": sea,
                    "val40": max(-1.0, CONFIG["inj_k"] * (gs40 - R))}
    return out


def roster_values(rows, season):
    """Minutes per game for each (team, player) in a season."""
    tot, games = {}, {}
    for r in rows:
        if r["season"] != season:
            continue
        games.setdefault(r["tid"], set()).add(r["gid"])
        if r["dnp"]:
            continue
        k = (r["tid"], r["pid"])
        tot[k] = tot.get(k, 0.0) + r["min"]
    return {k: v / max(1, len(games.get(k[0], ()))) for k, v in tot.items()}


def allocate_value(players, vals, newcomer=0.0):
    """Value of a group of players: minutes in order of their usual role, 200 per game in total."""
    lst = sorted(((m, vals[p]["val40"] if p in vals else newcomer) for p, m in players.items()), reverse=True)
    left, v = 200.0, 0.0
    for m, val in lst:
        take = min(m, left, CONFIG["max_minutes"])
        if take <= 0:
            break
        v += val * take / 40
        left -= take
    return v


def roster_prior_shift(db, cur, vals_last, current_team_of, rosters=None, newcomer_mpg=10.0):
    """Margin points per game each D1 team gained or lost since last season through roster moves.

    current_team_of: pid -> team for players seen this season (box scores) or on a current roster.
    Teams with too little information get no shift."""
    last_mpg = roster_values(db.pbox, cur - 1)
    by_team_last, pl_mpg = {}, {}
    for (t, p), m in last_mpg.items():
        by_team_last.setdefault(t, {})[p] = m
        pl_mpg[p] = max(pl_mpg.get(p, 0.0), m)
    now_by_team = {}
    for p, t in current_team_of.items():
        now_by_team.setdefault(t, {})[p] = pl_mpg.get(p, newcomer_mpg)
    for t, ros in (rosters or {}).items():
        for p in ros:
            if current_team_of.get(p, t) == t:
                now_by_team.setdefault(t, {}).setdefault(p, pl_mpg.get(p, newcomer_mpg))
    shift = {}
    for t in db.conf:
        now = now_by_team.get(t, {})
        if len(now) < 7 or t not in by_team_last:
            continue
        v_now = allocate_value(now, vals_last, newcomer=CONFIG.get("newcomer_val", 0.4))
        v_last = allocate_value(by_team_last[t], vals_last)
        shift[t] = max(-10.0, min(10.0, v_now - v_last))
    return shift


def build_prior(db, last_m, shift):
    """Preseason ratings: last season pulled toward its (current) conference's level, plus roster moves."""
    if not last_m:
        return {}
    k, kc, kp = CONFIG["prior_regress"], CONFIG["conf_regress"], CONFIG["pace_prior_regress"]
    to100 = 100 / max(55.0, last_m["mu_p"] * 1.0 + 0.0) if last_m.get("mu_p") else 1.45
    by_conf = {}
    for t, cid in db.conf.items():
        if t in last_m["o"]:
            by_conf.setdefault(cid, []).append(t)
    cm = {cid: (np.mean([last_m["o"][t] for t in ts]), np.mean([last_m["d"][t] for t in ts])) for cid, ts in by_conf.items()}
    o, d, pc = {}, {}, {}
    sw = CONFIG["roster_shift_w"]
    for t, cid in db.conf.items():
        mo, md = cm.get(cid, (-2.0, -2.0))
        lo, ld = last_m["o"].get(t), last_m["d"].get(t)
        sh = sw * shift.get(t, 0.0) * to100 / 2
        if lo is None:  # new to Division I (or no data last season): start below its conference
            o[t], d[t] = kc * mo - 2.0, kc * md - 2.0
        else:
            o[t] = kc * mo + k * (lo - mo) + sh
            d[t] = kc * md + k * (ld - md) + sh
        pc[t] = kp * last_m["p"].get(t, 0.0)
    if NOND1 in last_m["o"]:
        o[NOND1], d[NOND1] = last_m["o"][NOND1], last_m["d"][NOND1]
    return {"mu": last_m["mu"], "hca": last_m["hca"], "mu_p": last_m["mu_p"], "o": o, "d": d, "p": pc,
            "o_new": -4.0, "d_new": -4.0}


class Availability:
    """Who has been playing for each team, so absences can be priced against what the ratings already know."""

    def __init__(self, db, cur):
        self.cur = cur
        self.team_games = {}   # tid -> [(date, gid)] this season
        self.played = {}       # gid -> {tid: {pid: minutes}}
        self.latest_team = {}  # pid -> (date, tid) this season
        self.last_team = {}    # pid -> tid last season (most minutes)
        mins_last = {}
        for r in db.pbox:
            if r["season"] == cur:
                if not r["dnp"]:
                    self.played.setdefault(r["gid"], {}).setdefault(r["tid"], {})[r["pid"]] = r["min"]
                if r["pid"] not in self.latest_team or r["date"] >= self.latest_team[r["pid"]][0]:
                    self.latest_team[r["pid"]] = (r["date"], r["tid"])
            elif r["season"] == cur - 1 and not r["dnp"]:
                k = (r["pid"], r["tid"])
                mins_last[k] = mins_last.get(k, 0.0) + r["min"]
        best = {}
        for (p, t), m in mins_last.items():
            if m > best.get(p, (0, None))[0]:
                best[p] = (m, t)
        self.last_team = {p: t for p, (m, t) in best.items()}
        for g in db.games.values():
            if g["season"] == cur:
                for t in (g["home"], g["away"]):
                    self.team_games.setdefault(t, []).append((g["date"], g["gid"]))
        for t in self.team_games:
            self.team_games[t].sort()

    def presence(self, tid, pid, date, lam, hl):
        """Share of the evidence behind tid's rating in which pid played (prior counts as 'played')."""
        num, den = lam, lam
        dd = ddate(date)
        for d, gid in self.team_games.get(tid, []):
            if d >= date:
                break
            w = 0.5 ** ((dd - ddate(d)).days / hl)
            den += w
            if pid in self.played.get(gid, {}).get(tid, {}):
                num += w
        return num / den

    def missed_streak(self, tid, pid, date):
        """(games missed in a row, his minutes per game when he plays) for a rotation player, else (0, mpg)."""
        games = [(d, gid) for d, gid in self.team_games.get(tid, []) if d < date]
        mins = [self.played.get(gid, {}).get(tid, {}).get(pid) for d, gid in games]
        played = [m for m in mins if m]
        mpg = sum(played) / len(played) if played else 0.0
        if len(played) < 2 or mpg < CONFIG["missed_min_mpg"]:
            return 0, mpg
        n = 0
        for m in reversed(mins):
            if m:
                break
            n += 1
        return n, mpg

    def recent_minutes(self, tid, pid, date, n=10):
        ms = []
        for d, gid in reversed(self.team_games.get(tid, [])):
            if d >= date:
                continue
            m = self.played.get(gid, {}).get(tid, {}).get(pid)
            if m:
                ms.append(m)
            if len(ms) >= n:
                break
        return sum(ms) / len(ms) if ms else None


def inferred_absences(av, tid, date, members=None):
    """College has no public injury report: players missing the team's last game(s) get a reduced chance to play.

    Returns {pid: (play probability, games missed, mpg)}."""
    members = members if members is not None else team_players_before(av, tid, date)
    out = {}
    probs = CONFIG["missed_play_prob"]
    for p in members:
        n, mpg = av.missed_streak(tid, p, date)
        if n >= 1:
            out[p] = (probs.get(min(n, 3), 0.12), n, mpg)
    return out


def team_players_before(av, tid, date):
    """Players who appeared for tid this season before date and whose last appearance was for tid."""
    seen = {}
    for t, games in av.team_games.items():
        for d, gid in games:
            if d >= date:
                break
            for p in av.played.get(gid, {}).get(t, {}):
                if p not in seen or d >= seen[p][0]:
                    seen[p] = (d, t)
    return {p for p, (d, t) in seen.items() if t == tid}


def availability_adjust(av, tid, date, play_prob, vals, mpg_last, lam, hl, members=None):
    """Margin points tid is worse than its rating says (positive = weaker), and the per-player detail.

    play_prob: pid -> probability of playing tonight (1.0 when healthy).
    """
    members = members if members is not None else team_players_before(av, tid, date)
    pool = set(members) | {p for p, pr in play_prob.items() if pr > 0 and av.latest_team.get(p, (None, tid))[1] == tid}
    total, detail = 0.0, []
    for p in pool:
        v = vals.get(p)
        if not v:
            continue
        mpg = av.recent_minutes(tid, p, date) or mpg_last.get(p) or v.get("mpg") or 0.0
        mpg = min(mpg, 36.0)
        if mpg < 6:
            continue
        # share of the rating's evidence with him on the floor; a newcomer counts as absent from it
        pres = av.presence(tid, p, date, lam, hl) if p in members else 0.0
        pp = play_prob.get(p, 1.0)
        imp = v["val40"] * mpg / 40
        a = imp * (pres - pp)
        if abs(a) >= 0.05:
            detail.append((p, a, imp, pres, pp, mpg))
        total += a
    total = max(-10.0, min(12.0, total))
    return total, sorted(detail, key=lambda x: -abs(x[1]))


# --------------------------------------------------------------------------
# Player model (props)
# --------------------------------------------------------------------------
BASE_STATS = ["pts", "reb", "ast", "fg3m", "stl", "blk", "tov"]
COMBOS = {"pra": ("pts", "reb", "ast"), "pr": ("pts", "reb"), "pa": ("pts", "ast"), "ra": ("reb", "ast")}
PROP_STATS = ["pts", "reb", "ast", "fg3m", "pra", "pr", "pa", "ra"]
STAT_NAMES = {"pts": "Points", "reb": "Rebounds", "ast": "Assists", "fg3m": "Threes", "pra": "Pts+Reb+Ast",
              "pr": "Pts+Reb", "pa": "Pts+Ast", "ra": "Reb+Ast", "stl": "Steals", "blk": "Blocks"}
DISP_PRIOR = {"pts": 2.0, "reb": 1.25, "ast": 1.3, "fg3m": 1.1, "pra": 2.4, "pr": 2.1, "pa": 2.2, "ra": 1.4,
              "stl": 1.05, "blk": 1.15, "tov": 1.1}


def stat_of(r, k):
    if k in COMBOS:
        return sum(r[x] for x in COMBOS[k])
    return r[k]


class PlayerIndex:
    def __init__(self, db, cur):
        self.cur = cur
        self.logs = {}  # pid -> rows (both seasons) sorted by date
        for r in db.pbox:
            if r["season"] in (cur - 1, cur):
                self.logs.setdefault(r["pid"], []).append(r)
        lg = {k: 0.0 for k in BASE_STATS}
        mins = 0.0
        for r in db.pbox:
            if r["season"] == cur - 1 and not r["dnp"] and r["min"] >= 10:
                mins += r["min"]
                for k in BASE_STATS:
                    lg[k] += r[k]
        self.lg_rate = {k: (lg[k] / mins if mins else 0.0) for k in BASE_STATS}
        if not mins:
            self.lg_rate = {"pts": 0.47, "reb": 0.18, "ast": 0.11, "fg3m": 0.055, "stl": 0.033, "blk": 0.022,
                            "tov": 0.06}

    def before(self, pid, date):
        return [r for r in self.logs.get(pid, []) if r["date"] < date]


def project_player(pi, pid, tid, date, cfg=None):
    """Baseline minutes, per-minute rates and dispersion for one player (before context scaling)."""
    cfg = cfg or CONFIG
    rows = pi.before(pid, date)
    cur = pi.cur
    played = [r for r in rows if not r["dnp"] and r["min"] > 0]
    if not played:
        return None
    # ---- minutes: recent games for his current team (coach's-decision DNPs count as 0) ----
    cur_team = [r for r in rows if r["season"] == cur and r["tid"] == tid
                and (not r["dnp"] or "COACH" in r["reason"].upper())]
    hl_m = cfg["minutes_hl_games"]
    wsum = msum = 0.0
    for i, r in enumerate(reversed(cur_team[-20:])):
        w = 0.5 ** (i / hl_m)
        wsum += w
        msum += w * (0.0 if r["dnp"] else r["min"])
    last = [r for r in played if r["season"] == cur - 1]
    m_last = sum(r["min"] for r in last) / len(last) if last else None
    if wsum and m_last is not None:
        k = 1.5
        m_base = (msum + k * m_last) / (wsum + k)
    elif wsum:
        m_base = msum / wsum
    elif m_last is not None:
        m_base = 0.9 * m_last
    else:
        return None
    m_cur = [r["min"] for r in cur_team if not r["dnp"]]
    m_sd_logs = float(np.std([r["min"] for r in played[-15:]])) if len(played) >= 4 else None
    # ---- per-minute rates (recency weighted, last season discounted) ----
    hl_p = cfg["player_hl_games"]
    acc = {k: 0.0 for k in BASE_STATS}
    accm = 0.0
    n = len(played)
    for i, r in enumerate(played):
        age = n - 1 - i
        w = 0.5 ** (age / hl_p) * (1.0 if r["season"] == cur else cfg["last_season_player_weight"])
        accm += w * r["min"]
        for k in BASE_STATS:
            acc[k] += w * r[k]
    prior_min = 60.0
    rate = {k: (acc[k] + pi.lg_rate[k] * prior_min * 0.8) / (accm + prior_min) for k in BASE_STATS}
    # ---- dispersion per minute, from residuals in his own game log ----
    disp = {}
    for k in BASE_STATS + list(COMBOS):
        rk = rate[k] if k in rate else sum(rate[x] for x in COMBOS[k])
        num = den = 0.0
        for i, r in enumerate(played[-40:]):
            e = rk * r["min"]
            num += (stat_of(r, k) - e) ** 2
            den += r["min"]
        prior = DISP_PRIOR[k] * rk
        pm = 400.0
        disp[k] = (num + prior * pm) / (den + pm) if den else prior
    cur_played = [r for r in played if r["season"] == cur]
    # recent form: this season only once he has 5 games (roles change over the summer)
    last10 = cur_played[-10:] if len(cur_played) >= 5 else played[-10:]
    seas = [r for r in played if r["season"] == cur]
    return {
        "pid": pid, "m_base": m_base, "m_last": m_last, "m_sd": m_sd_logs,
        "m_l5": (sum(m_cur[-5:]) / len(m_cur[-5:]) if m_cur else None),
        "m_season": (sum(m_cur) / len(m_cur) if m_cur else None),
        "rate": rate, "disp": disp, "n_cur": len(seas), "n_all": len(played),
        "gp_cur": len(seas),
        "avg_cur": {k: (sum(stat_of(r, k) for r in seas) / len(seas) if seas else None) for k in PROP_STATS},
        "avg_last": {k: (sum(stat_of(r, k) for r in last) / len(last) if last else None) for k in PROP_STATS},
        "l10": {k: [stat_of(r, k) for r in last10] for k in PROP_STATS},
        "l10_min": [r["min"] for r in last10],
        "starter_share": (sum(1 for r in played[-10:] if r["starter"]) / min(10, len(played))),
    }


def team_minutes(players, total=200.0, cap=None):
    """Scale expected minutes so the team plays `total`, capping heavy-minute players."""
    cap = cap or CONFIG["max_minutes"]
    m = {p: x for p, x in players.items() if x > 0}
    for _ in range(6):
        s_ = sum(m.values())
        if s_ <= 0:
            return m
        f = total / s_
        f = 1 + CONFIG["min_scale_alpha"] * (f - 1)
        f = max(0.70, min(1.40, f))
        new = {p: min(cap, x * f) for p, x in m.items()}
        m = new
        break
    return m


def game_players(pi, av, tid, date, play_prob, team_pts, opp_ctx, pace_ratio, margin, roster=None):
    """Projected minutes and stat distributions for one team's players in one game."""
    cand = set(team_players_before(av, tid, date))
    if roster:
        cand |= {p for p in roster if p in pi.logs}
    elif not cand:
        # no games yet and no roster: last season's players who haven't turned up anywhere else
        cand = {p for p, t in av.last_team.items() if t == tid and p not in av.latest_team}
    base = {}
    for p in cand:
        if play_prob.get(p, 1.0) <= 0:
            continue
        lt = av.latest_team.get(p)
        if lt and lt[1] != tid and (not roster or p not in roster):
            continue
        b = project_player(pi, p, tid, date)
        if b and b["m_base"] >= 3:
            base[p] = b
    if not base:
        return []
    exp_min = {p: b["m_base"] * play_prob.get(p, 1.0) for p, b in base.items()}
    # blowout risk trims starters' minutes a little
    blow = max(0.0, abs(margin) - 12.0)
    if blow:
        for p, b in base.items():
            if b["m_base"] >= 26:
                exp_min[p] *= max(0.88, 1 - 0.008 * blow)
    p_ot = CONFIG.get("_p_ot", 0.055)
    mins = team_minutes(exp_min, total=200.0 * (1 + p_ot * 5 / 40))
    # context: scale points so players add up to the team's projected points
    raw_pts = sum(mins.get(p, 0) * b["rate"]["pts"] for p, b in base.items())
    f_pts = max(0.85, min(1.18, team_pts / raw_pts)) if raw_pts > 0 else 1.0
    f_ctx = {"pts": f_pts, "fg3m": f_pts ** 0.8, "reb": pace_ratio * opp_ctx.get("reb", 1.0),
             "ast": pace_ratio * opp_ctx.get("ast", 1.0) ** 0.5, "stl": pace_ratio, "blk": pace_ratio,
             "tov": pace_ratio}
    out = []
    for p, b in base.items():
        m = mins.get(p, 0.0)
        pp = play_prob.get(p, 1.0)
        m_play = m / pp if pp > 0 else 0.0  # minutes if he plays
        if m_play < 1:
            continue
        msd = b["m_sd"] if b["m_sd"] is not None else 0.2 * m_play
        msd = max(2.5, min(msd, 0.35 * m_play))
        res = {"pid": p, "min": m_play, "min_sd": msd, "pp": pp, "base": b, "mean": {}, "var": {}}
        vm, cvs, bias = CONFIG["prop_var_mult"], CONFIG["prop_mean_cv"], CONFIG["prop_bias"]
        for k in BASE_STATS + list(COMBOS):
            if k in COMBOS:
                r = sum(b["rate"][x] * f_ctx.get(x, 1.0) * bias.get(x, 1.0) for x in COMBOS[k])
                cv = max(cvs.get(x, cvs["default"]) for x in COMBOS[k]) * 0.85
            else:
                r = b["rate"][k] * f_ctx.get(k, 1.0) * bias.get(k, 1.0)
                cv = cvs.get(k, cvs["default"])
            mu = r * m_play
            res["mean"][k] = mu
            res["var"][k] = vm * (b["disp"][k] * m_play + (r * msd) ** 2) + (cv * mu) ** 2
        out.append(res)
    out.sort(key=lambda x: -x["min"])
    return out


def prop_line_info(mu, var):
    """Fair line and the over/under thresholds where a -110 bet has an edge (cautious)."""
    buf = CONFIG["buffer_props"]
    need = 110 / 210 + buf  # break-even at -110 plus a safety margin
    kmax = int(mu + 6 * math.sqrt(max(var, mu, 1)) + 5)
    cdf = count_cdf_table(mu, max(var, 1e-6), kmax)

    def p_over(line):
        k = int(math.floor(line))
        return 1.0 if k < 0 else 1 - cdf[min(k, kmax)]
    lines = [x + 0.5 for x in range(0, kmax)]
    fair = min(lines, key=lambda L: abs(p_over(L) - 0.5)) if lines else 0.5
    over_upto = max([L for L in lines if p_over(L) >= need], default=None)
    under_from = min([L for L in lines if 1 - p_over(L) >= need], default=None)
    return fair, over_upto, under_from, p_over


# --------------------------------------------------------------------------
# Slate, injuries, context
# --------------------------------------------------------------------------
def slate_from_release(db, d):
    out = []
    for r in db.sched_upcoming:
        if str(r.get("game_date"))[:10] != d.isoformat():
            continue
        try:
            h, a = int(r["home_id"]), int(r["away_id"])
        except (TypeError, ValueError):
            continue
        if h not in db.conf and a not in db.conf:
            continue
        utc = parse_utc(r.get("date"))
        out.append({"gid": str(r["game_id"]), "utc": utc, "date": d.isoformat(), "state": "pre",
                    "completed": False, "detail": "", "home": h, "away": a,
                    "habbr": r.get("home_abbreviation"), "aabbr": r.get("away_abbreviation"), "hs": None,
                    "as": None, "hrec": None, "arec": None, "neutral": bool(r.get("neutral_site")),
                    "venue": r.get("venue_full_name") or "", "tv": "", "odds": None, "stype": 2,
                    "note": r.get("notes_headline") or "", "conf_game": bool(r.get("conference_competition")),
                    "hrank": db.rank.get(h), "arank": db.rank.get(a)})
    return out


def load_slate(api, db, today, days):
    games = []
    espn_ok = 0
    for i in range(days):
        d = today + dt.timedelta(days=i)
        evs = fetch_scoreboard(api, d, i <= 1) if not OFFLINE or os.path.exists(
            os.path.join(DIRS["sb"], f"sb_{d.strftime('%Y%m%d')}.json")) else []
        evs = [e for e in evs if (e["date"] == d.isoformat() or e["date"] is None)
               and (e["home"] in db.conf or e["away"] in db.conf or e.get("hconf") or e.get("aconf"))]
        for e in evs:
            note_scoreboard_teams(db, e)
        if evs:
            espn_ok += 1
        else:
            evs = slate_from_release(db, d)
        for e in evs:
            e["date"] = d.isoformat()
            games.append(e)
    return games, espn_ok


def play_prob(inj, gdate):
    st = (inj.get("status") or "").lower()
    pmap = CONFIG["status_play"]
    p = None
    for k, v in pmap.items():
        if k in st:
            p = v
            break
    if p is None:
        p = 0.0 if "out" in st else 0.6
    ret = inj.get("ret")
    if p == 0.0 and ret and ret[:10] <= gdate and "suspen" not in st:
        p = 0.5
    return p


class Ctx:
    pass


def build_context(api, db, today, slate, no_injuries=False, no_rosters=False):
    c = Ctx()
    c.db, c.today, c.cur = db, today, season_for(today)
    asof = today.isoformat()
    extra = [(g["date"], g["home"], g["away"]) for g in slate]
    c.tdates = team_dates(db, extra)
    c.av = Availability(db, c.cur)
    c.pi = PlayerIndex(db, c.cur)
    c.vals = player_values([r for r in db.pbox if r["season"] in (c.cur - 1, c.cur)], asof, c.cur)
    tmp = {}
    for r in db.pbox:
        if r["season"] == c.cur - 1 and not r["dnp"]:
            a = tmp.setdefault(r["pid"], [0.0, 0])
            a[0] += r["min"]
            a[1] += 1
    c.mpg_last = {p: m / n for p, (m, n) in tmp.items()}
    # current rosters: only needed for teams that have barely played (box scores cover everyone else)
    gp = {}
    for g in db.games.values():
        if g["season"] == c.cur:
            for t in (g["home"], g["away"]):
                gp[t] = gp.get(t, 0) + 1
    need = sorted({t for g in slate for t in (g["home"], g["away"]) if t in db.conf and gp.get(t, 0) < 3})
    c.rosters = {} if (no_rosters or OFFLINE or not need) else fetch_rosters(api, need)
    c.inj = {} if no_injuries else fetch_injuries(api)
    c.inj_ok = bool(c.inj)
    last_m = last_season_prior(db, c.cur)
    vals_last = player_values([r for r in db.pbox if r["season"] == c.cur - 1], f"{c.cur - 1}-07-01", c.cur - 1)
    cto = {p: t for p, (d, t) in c.av.latest_team.items()}
    for t, ros in c.rosters.items():
        for p in ros:
            cto.setdefault(p, t)
    c.shift = roster_prior_shift(db, c.cur, vals_last, cto, c.rosters) if last_m else {}
    prior = build_prior(db, last_m, c.shift)
    c.recs = [r for r in game_records(db, {c.cur}) if r["stype"] in (2, 3)]
    c.model = fit_team_model(c.recs, asof, prior, teams=list(db.conf))
    c.last_model = last_m
    c.n_cur_games = sum(1 for r in c.recs if r["home"] in db.conf and r["away"] in db.conf)
    c.gp = gp
    c.inj_team = {}
    for k, x in c.inj.items():
        pid, tid = x.get("pid"), x.get("tid")
        if pid and pid in c.av.latest_team:
            tid = c.av.latest_team[pid][1]
        if tid:
            c.inj_team.setdefault(tid, []).append(x)
    c.team_stats = team_table(c)
    return c


def team_table(c):
    """Season-to-date stats, records, ATS, conference standing and ranks for every Division I team."""
    db, cur, m = c.db, c.cur, c.model
    T = {}
    for t in db.conf:
        meta = db.teams.get(t, {})
        cid = db.conf[t]
        T[t] = {"id": t, "abbr": meta.get("abbr") or str(t), "name": meta.get("name") or str(t),
                "short": meta.get("short") or meta.get("name") or str(t), "color": meta.get("color") or "555555",
                "logo": meta.get("logo") or "", "conf_id": cid, "conf": CONF_NAMES.get(cid, ("?", "?"))[0],
                "rank": db.rank.get(t), "w": 0, "l": 0, "cw": 0, "cl": 0, "hw": 0, "hl": 0, "aw": 0, "al": 0,
                "nw": 0, "nl": 0, "res": [], "pf": 0.0, "pa": 0.0, "poss": 0.0, "g": 0, "mins": 0.0,
                "ats": [0, 0, 0], "ou": [0, 0, 0], "fga": 0, "fgm": 0, "fg3m": 0, "fg3a": 0, "fta": 0, "ftm": 0,
                "oreb": 0, "dreb": 0, "tov": 0, "ofga": 0, "ofgm": 0, "ofg3m": 0, "ofg3a": 0, "ofta": 0,
                "otov": 0, "ooreb": 0, "odreb": 0, "reb": 0, "ast": 0, "oreb_all": 0, "oast": 0}
    for r in c.recs:
        ln = db.lines.get(r["gid"]) or {}
        for t, o, pf, pa, home, b, ob in ((r["home"], r["away"], r["hs"], r["as"], True, r["th"], r["ta"]),
                                          (r["away"], r["home"], r["as"], r["hs"], False, r["ta"], r["th"])):
            if t not in T:
                continue
            x = T[t]
            win = pf > pa
            x["w" if win else "l"] += 1
            if r.get("conf_game"):
                x["cw" if win else "cl"] += 1
            loc = "n" if r["neutral"] else ("h" if home else "a")
            x[loc + ("w" if win else "l")] += 1
            x["g"] += 1
            x["pf"] += pf
            x["pa"] += pa
            x["poss"] += r["poss"]
            x["mins"] += r["mins"]
            for k in ("fga", "fgm", "fg3m", "fg3a", "fta", "ftm", "oreb", "dreb", "tov", "reb", "ast"):
                x[k] += b[k]
            for k in ("fga", "fgm", "fg3m", "fg3a", "fta", "tov", "oreb", "dreb"):
                x["o" + k] += ob[k]
            x["oreb_all"] += ob["reb"]
            x["oast"] += ob["ast"]
            ats = ou = None
            if ln.get("sp") is not None:
                line = ln["sp"] if home else -ln["sp"]
                v = (pf - pa) + line
                ats = "W" if v > 0 else ("L" if v < 0 else "P")
                x["ats"]["WLP".index(ats)] += 1
            if ln.get("tot") is not None:
                v = (pf + pa) - ln["tot"]
                ou = "O" if v > 0 else ("U" if v < 0 else "P")
                x["ou"]["OUP".index(ou)] += 1
            x["res"].append({"date": r["date"], "opp": o, "home": home, "neutral": r["neutral"], "pf": pf, "pa": pa,
                             "win": win, "ats": ats, "ou": ou,
                             "line": (ln.get("sp") if home else (-ln["sp"] if ln.get("sp") is not None else None)),
                             "tot": ln.get("tot"), "net": 100 * (pf - pa) / r["poss"]})
    for t, x in T.items():
        g = max(1, x["g"])
        poss = max(1.0, x["poss"])
        has = x["g"] > 0
        x["ortg"] = 100 * x["pf"] / poss if has else None
        x["drtg"] = 100 * x["pa"] / poss if has else None
        x["net"] = (x["ortg"] - x["drtg"]) if has else None
        x["pace"] = x["poss"] * 40 / x["mins"] if x["mins"] else None
        x["ppg"] = x["pf"] / g if has else None
        x["oppg"] = x["pa"] / g if has else None
        x["efg"] = (x["fgm"] + 0.5 * x["fg3m"]) / x["fga"] if x["fga"] else None
        x["oefg"] = (x["ofgm"] + 0.5 * x["ofg3m"]) / x["ofga"] if x["ofga"] else None
        x["tovp"] = x["tov"] / poss if has else None
        x["otovp"] = x["otov"] / poss if has else None
        x["orbp"] = x["oreb"] / (x["oreb"] + x["odreb"]) if x["oreb"] + x["odreb"] else None
        x["drbp"] = x["dreb"] / (x["dreb"] + x["ooreb"]) if x["dreb"] + x["ooreb"] else None
        x["ftr"] = x["fta"] / x["fga"] if x["fga"] else None
        x["oftr"] = x["ofta"] / x["ofga"] if x["ofga"] else None
        x["3par"] = x["fg3a"] / x["fga"] if x["fga"] else None
        x["3pct"] = x["fg3m"] / x["fg3a"] if x["fg3a"] else None
        x["o3pct"] = x["ofg3m"] / x["ofg3a"] if x["ofg3a"] else None
        x["adj_o"] = m["mu"] + rating(m, t, "o")
        x["adj_d"] = m["mu"] - rating(m, t, "d")
        x["adj_net"] = rating(m, t, "o") + rating(m, t, "d")
        x["adj_pace"] = m["mu_p"] + 2 * rating(m, t, "p")
        l10 = x["res"][-10:]
        x["l10"] = f"{sum(1 for r in l10 if r['win'])}-{sum(1 for r in l10 if not r['win'])}"
        x["l10_net"] = sum(r["net"] for r in l10) / len(l10) if l10 else None
        st = ""
        n = 0
        for r in reversed(x["res"]):
            ch = "W" if r["win"] else "L"
            if not st:
                st = ch
            if ch != st:
                break
            n += 1
        x["streak"] = f"{st}{n}" if st else ""
        x["pct"] = x["w"] / (x["w"] + x["l"]) if x["w"] + x["l"] else 0.0
        x["shift"] = c.shift.get(t, 0.0)
        x["oreb_pg"] = x["oreb_all"] / g if has else None
        x["oast_pg"] = x["oast"] / g if has else None
    higher_better = ["ortg", "net", "pace", "efg", "otovp", "orbp", "drbp", "ftr", "3par", "3pct", "ppg",
                     "adj_o", "adj_net", "adj_pace", "l10_net"]
    lower_better = ["drtg", "oefg", "tovp", "oftr", "o3pct", "oppg", "adj_d"]
    for k in higher_better + lower_better:
        vals = sorted([x[k] for x in T.values() if x.get(k) is not None and (x["g"] or k.startswith("adj"))],
                      reverse=k in higher_better)
        pos = {}
        for i, v in enumerate(vals):
            pos.setdefault(v, i + 1)
        for x in T.values():
            x["rk_" + k] = pos.get(x[k]) if x.get(k) is not None and (x["g"] or k.startswith("adj")) else None
    for cid in set(db.conf.values()):
        cs = sorted([x for x in T.values() if x["conf_id"] == cid],
                    key=lambda x: (-(x["cw"] - x["cl"]), -x["pct"], -x["adj_net"]))
        for i, x in enumerate(cs):
            x["conf_rank"] = i + 1
            x["conf_n"] = len(cs)
    for i, x in enumerate(sorted(T.values(), key=lambda x: -x["adj_net"])):
        x["power"] = i + 1
    return T


# --------------------------------------------------------------------------
# Markets
# --------------------------------------------------------------------------
def ninv(p):
    lo, hi = -8.0, 8.0
    for _ in range(60):
        mid = (lo + hi) / 2
        if ncdf(mid) < p:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def market(key, group, label, pw, pp, pl, buf, book=None, book_line=None, line=None, mkt_p=None,
           model_p=None, grade=None, est_line=False, mu=None, sd=None, kind="normal", extra=None):
    pw, pp, pl = max(0.0, pw), max(0.0, pp), max(0.0, pl)
    fair = fair_from(pw, pl)
    pwc, plc = max(0.001, pw - buf), min(0.999, pl + buf)
    bet_at = fair_from(pwc, plc)
    m = {"key": key, "group": group, "label": label, "p": pw, "push": pp, "pl": pl, "fair": fair,
         "bet_at": bet_at, "book": book, "line": line, "mkt_p": mkt_p, "model_p": model_p, "grade": grade,
         "est_line": est_line, "mu": mu, "sd": sd, "kind": kind, "buf": buf, "ev": None, "ev_c": None,
         "verdict": None}
    if extra:
        m.update(extra)
    if book is not None:
        m["ev"] = ev_of(pw, pl, book)
        m["ev_c"] = ev_of(pwc, plc, book)
        m["verdict"] = "value" if m["ev_c"] > 0 else ("lean" if m["ev"] > 0 else "avoid")
    return m


def fsp(team, x):
    """'BOS -4.5', 'BOS +3', or 'BOS PK' for a spread from the team's side."""
    x = round(x * 10) / 10
    if abs(x) < 0.05:
        return f"{team} PK"
    return f"{team} {x:+g}"


def round_half(x):
    return math.floor(x) + 0.5


def spread_threshold(mm, w, sd, side_home=True):
    """Market margin at which a -110 spread bet becomes worth it, given the model margin mm."""
    z = ninv(110 / 210 + CONFIG["buffer_main"])
    gap = sd * z / max(w, 0.05)
    return (mm - gap) if side_home else (mm + gap)


def game_markets(g, mm, mt, sp_line, tot_line, odds):
    """mm/mt = pure model margin (home - away) and total. sp_line = home spread from the book."""
    C = CONFIG
    wm, wt = C["w_model_margin"], C["w_model_total"]
    has_sp, has_tot = sp_line is not None, tot_line is not None
    mkt_margin = -sp_line if has_sp else None
    bm = wm * mm + (1 - wm) * mkt_margin if has_sp else mm
    bt = wt * mt + (1 - wt) * tot_line if has_tot else mt
    sdm = C["sd_margin"] if has_sp else C["sd_margin"] + 0.6
    sdt = C["sd_total"] if has_tot else C["sd_total"] + 0.4
    H, A = g["habbr"], g["aabbr"]
    out = []
    ml = (odds or {}).get("ml") or {}
    nv_h, nv_a = novig(ml.get("H"), ml.get("A"))
    ph = ncdf(bm / sdm)
    pm_h = ncdf(mm / (C["sd_margin"] + 0.6))
    out.append(market("ml_H", "Moneyline", f"{H} ML", ph, 0, 1 - ph, C["buffer_main"], ml.get("H"),
                      mkt_p=nv_h, model_p=pm_h, grade={"t": "ml", "side": "H"}))
    out.append(market("ml_A", "Moneyline", f"{A} ML", 1 - ph, 0, ph, C["buffer_main"], ml.get("A"),
                      mkt_p=nv_a, model_p=1 - pm_h, grade={"t": "ml", "side": "A"}))
    sp = (odds or {}).get("sp") or {}
    L = sp_line if has_sp else -round(mm * 2) / 2
    hi, pu, lo = line_probs(bm, sdm, -L)
    mhi, _, mlo = line_probs(mm, C["sd_margin"] + 0.6, -L)
    nvh, nva = novig(sp.get("H", (None, None))[1], sp.get("A", (None, None))[1])
    out.append(market("sp_H", "Spread", f"{H} {L:+g}" if L else f"{H} PK", hi, pu, lo, C["buffer_main"],
                      sp.get("H", (None, None))[1], line=L, mkt_p=nvh, model_p=mhi, est_line=not has_sp,
                      grade={"t": "sp", "side": "H", "line": L}, mu=bm, sd=sdm, kind="margin", extra={"side": "H"}))
    out.append(market("sp_A", "Spread", f"{A} {-L:+g}" if L else f"{A} PK", lo, pu, hi, C["buffer_main"],
                      sp.get("A", (None, None))[1], line=-L, mkt_p=nva, model_p=mlo, est_line=not has_sp,
                      grade={"t": "sp", "side": "A", "line": L}, mu=-bm, sd=sdm, kind="margin", extra={"side": "A"}))
    TL = tot_line if has_tot else round_half(mt)
    tot = (odds or {}).get("tot")
    hi, pu, lo = line_probs(bt, sdt, TL)
    mhi, _, mlo = line_probs(mt, C["sd_total"] + 0.4, TL)
    nvo, nvu = novig(tot[1], tot[2]) if tot else (None, None)
    out.append(market("tot_O", "Total", f"Over {TL:g}", hi, pu, lo, C["buffer_total"], tot[1] if tot else None,
                      line=TL, mkt_p=nvo, model_p=mhi, est_line=not has_tot, grade={"t": "tot", "side": "O", "line": TL},
                      mu=bt, sd=sdt, kind="total", extra={"side": "O"}))
    out.append(market("tot_U", "Total", f"Under {TL:g}", lo, pu, hi, C["buffer_total"], tot[2] if tot else None,
                      line=TL, mkt_p=nvu, model_p=mlo, est_line=not has_tot, grade={"t": "tot", "side": "U", "line": TL},
                      mu=bt, sd=sdt, kind="total", extra={"side": "U"}))
    # derived markets (lines estimated from the main market; edit the line on the board)
    mk_tot = tot_line if has_tot else mt
    mk_mar = mkt_margin if has_sp else mm
    for side, ab, sign in (("H", H, 1), ("A", A, -1)):
        mu = (bt + sign * bm) / 2
        line = round_half((mk_tot + sign * mk_mar) / 2 - 0.5) if True else None
        hi, pu, lo = line_probs(mu, C["sd_team"], line)
        out.append(market(f"tt_{side}_O", "Team total", f"{ab} over {line:g}", hi, pu, lo, C["buffer_derived"],
                          line=line, est_line=True, grade={"t": "tt", "side": side, "ou": "O", "line": line},
                          mu=mu, sd=C["sd_team"], kind="total", extra={"side": "O"}))
        out.append(market(f"tt_{side}_U", "Team total", f"{ab} under {line:g}", lo, pu, hi, C["buffer_derived"],
                          line=line, est_line=True, grade={"t": "tt", "side": side, "ou": "U", "line": line},
                          mu=mu, sd=C["sd_team"], kind="total", extra={"side": "U"}))
    for per, nm in (("1h", "1st half"),):
        share, mshare = C[f"share_{per}"], C[f"margin_{per}"]
        smu, tmu = bm * mshare, bt * share
        sdm_p, sdt_p = C[f"sd_{per}_margin"], C[f"sd_{per}_total"]
        Lp = round(mk_mar * mshare * 2) / 2
        Lp = -Lp if Lp else 0.0  # home line
        if abs(Lp - round(Lp)) < 1e-9 and Lp != 0:
            Lp += 0.5 if Lp > 0 else -0.5
        hi, pu, lo = line_probs(smu, sdm_p, -Lp)
        out.append(market(f"{per}_sp_H", nm, f"{nm.capitalize()} {H} {Lp:+g}" if Lp else f"{nm.capitalize()} {H} PK",
                          hi, pu, lo, C["buffer_derived"], line=Lp, est_line=True,
                          grade={"t": per + "_sp", "side": "H", "line": Lp}, mu=smu, sd=sdm_p, kind="margin",
                          extra={"side": "H"}))
        out.append(market(f"{per}_sp_A", nm, f"{nm.capitalize()} {A} {-Lp:+g}" if Lp else f"{nm.capitalize()} {A} PK",
                          lo, pu, hi, C["buffer_derived"], line=-Lp, est_line=True,
                          grade={"t": per + "_sp", "side": "A", "line": Lp}, mu=-smu, sd=sdm_p, kind="margin",
                          extra={"side": "A"}))
        TLp = round_half(mk_tot * share - 0.5)
        hi, pu, lo = line_probs(tmu, sdt_p, TLp)
        out.append(market(f"{per}_tot_O", nm, f"{nm.capitalize()} over {TLp:g}", hi, pu, lo, C["buffer_derived"],
                          line=TLp, est_line=True, grade={"t": per + "_tot", "side": "O", "line": TLp},
                          mu=tmu, sd=sdt_p, kind="total", extra={"side": "O"}))
        out.append(market(f"{per}_tot_U", nm, f"{nm.capitalize()} under {TLp:g}", lo, pu, hi, C["buffer_derived"],
                          line=TLp, est_line=True, grade={"t": per + "_tot", "side": "U", "line": TLp},
                          mu=tmu, sd=sdt_p, kind="total", extra={"side": "U"}))
    return out, bm, bt


# --------------------------------------------------------------------------
# One game
# --------------------------------------------------------------------------
def team_play_probs(c, tid, gdate):
    pp = {}
    ros = c.rosters.get(tid)
    if ros:
        for p in ros:
            pp[p] = 1.0
    injured = []
    if tid in c.db.conf:
        for pid, (pr, n, mpg) in inferred_absences(c.av, tid, gdate).items():
            name = c.db.pnames.get(pid, ("?",))[0]
            pp[pid] = pr
            injured.append({"pid": pid, "name": name, "tid": tid, "status": f"Missed last {n}" if n > 1 else "Missed last game",
                            "detail": f"{mpg:.0f} min/game when he plays", "ret": "", "note": "", "pp": pr,
                            "inferred": True, "missed": n})
    for x in c.inj_team.get(tid, []):
        pid = x.get("pid")
        if not pid:
            continue
        pr = play_prob(x, gdate)
        pp[pid] = pr
        injured.append({**x, "pp": pr})
    return pp, injured


def analyze_game(c, g, props_book):
    m, db, T = c.model, c.db, c.team_stats
    h, a, d = g["home"], g["away"], g["date"]
    rh, ra = rest_days(c.tdates, h, d), rest_days(c.tdates, a, d)
    hb, ab = rh == 1, ra == 1
    pp_h, inj_h = team_play_probs(c, h, d)
    pp_a, inj_a = team_play_probs(c, a, d)
    lam, hl = m["lam"], CONFIG["hl_days"]
    d1h, d1a = h in db.conf, a in db.conf
    adj_h, det_h = availability_adjust(c.av, h, d, pp_h, c.vals, c.mpg_last, lam, hl) if d1h else (0.0, [])
    adj_a, det_a = availability_adjust(c.av, a, d, pp_a, c.vals, c.mpg_last, lam, hl) if d1a else (0.0, [])
    pg = predict_game(m, db.mid(h), db.mid(a), g["neutral"], hb, ab, adj_h, adj_a)
    CONFIG["_p_ot"] = pg["p_ot"]
    mm, mt = pg["ph"] - pg["pa"], pg["ph"] + pg["pa"]
    odds = g.get("odds") or {}
    sp_line = (odds.get("sp") or {}).get("H", (None,))[0] if odds.get("sp") else None
    tot_line = odds["tot"][0] if odds.get("tot") else None
    mkts, bm, bt = game_markets(g, mm, mt, sp_line, tot_line, odds)
    # a big model vs market gap usually means news the model can't see: those bets are flagged, not recommended
    side_gap = abs(mm + sp_line) if sp_line is not None else 0.0
    tot_gap = abs(mt - tot_line) if tot_line is not None else 0.0
    for mk_ in mkts:
        if (mk_["group"] in ("Spread", "Moneyline") and side_gap > CONFIG["max_gap_pts"]) or \
                (mk_["group"] == "Total" and tot_gap > CONFIG["max_gap_pts_total"]):
            mk_["gap"] = True
            if mk_["verdict"] in ("value", "lean"):
                mk_["verdict"] = "gap"
    # players
    tp_h, tp_a = (bt + bm) / 2, (bt - bm) / 2
    ctx_h = opp_context(T, a)
    ctx_a = opp_context(T, h)
    pace_h = pg["pace"] / max(55.0, m["mu_p"] + 2 * rating(m, db.mid(h), "p"))
    pace_a = pg["pace"] / max(55.0, m["mu_p"] + 2 * rating(m, db.mid(a), "p"))
    pl_h = game_players(c.pi, c.av, h, d, pp_h, tp_h, ctx_h, pace_h, bm, c.rosters.get(h)) if d1h else []
    pl_a = game_players(c.pi, c.av, a, d, pp_a, tp_a, ctx_a, pace_a, -bm, c.rosters.get(a)) if d1a else []
    props = []
    for side, plist, tid, opp in (("H", pl_h, h, a), ("A", pl_a, a, h)):
        for x in plist:
            if x["min"] < CONFIG["min_proj_minutes"] and not any(
                    (x["pid"], k) in props_book for k in PROP_STATS):
                continue
            props.append(player_props(c, x, tid, opp, g, props_book))
    inj_detail = {}
    for tid, det, injured in ((h, det_h, inj_h), (a, det_a, inj_a)):
        impact = {p: (adj, imp) for p, adj, imp, pres, pp, mpg in det}
        rows = []
        for x in injured:
            pid = x.get("pid")
            v = c.vals.get(pid, {})
            mp = c.av.recent_minutes(tid, pid, d) or c.mpg_last.get(pid)
            rows.append({**x, "mpg": mp, "adj": impact.get(pid, (0.0, 0.0))[0],
                         "imp": impact.get(pid, (0.0, v.get("val40", 0) * (mp or 0) / 40))[1],
                         "ppg": (c.pi.logs and _season_avg(c.pi, pid, c.cur, "pts"))})
        rows.sort(key=lambda r: -(r["imp"] or 0))
        returning = [(p, adj) for p, adj, imp, pres, pp, mpg in det if adj < -0.3 and pp > 0.5]
        inj_detail[tid] = {"rows": rows, "total": adj_h if tid == h else adj_a, "returning": returning}
    return {
        "g": g, "pred": pg, "mm": mm, "mt": mt, "bm": bm, "bt": bt, "markets": mkts, "props": props,
        "rest": (rh, ra), "b2b": (hb, ab), "adj": (adj_h, adj_a), "inj": inj_detail,
        "players": {h: pl_h, a: pl_a}, "sp_line": sp_line, "tot_line": tot_line,
        "h2h": head_to_head(c, h, a), "win_h": ncdf(bm / CONFIG["sd_margin"]), "d1": (d1h, d1a),
    }


def _season_avg(pi, pid, cur, k):
    rows = [r for r in pi.logs.get(pid, []) if not r["dnp"] and r["min"] > 0]
    cs = [r for r in rows if r["season"] == cur] or [r for r in rows if r["season"] == cur - 1]
    return sum(stat_of(r, k) for r in cs) / len(cs) if cs else None


_LG = {}


def opp_context(T, opp):
    o = T.get(opp) or {}
    if id(T) not in _LG:
        played = [x for x in T.values() if x["g"]]
        _LG.clear()
        _LG[id(T)] = (np.mean([x["oreb_pg"] for x in played]) if played else None,
                      np.mean([x["oast_pg"] for x in played]) if played else None)
    lg_reb, lg_ast = _LG[id(T)]
    ctx = {}
    if lg_reb and o.get("g", 0) >= 3:
        wgt = min(1.0, o["g"] / 20)
        ctx["reb"] = 1 + wgt * (o["oreb_pg"] / lg_reb - 1) * 0.5
        ctx["ast"] = 1 + wgt * (o["oast_pg"] / lg_ast - 1) * 0.5
    return ctx


def player_props(c, x, tid, opp, g, props_book):
    b = x["base"]
    name, short, pos = c.db.pnames.get(x["pid"], ("?", "?", ""))
    out = {"pid": x["pid"], "name": name, "short": short, "pos": pos, "tid": tid, "opp": opp,
           "gid": g["gid"], "date": g["date"], "min": x["min"], "pp": x["pp"], "m_l5": b["m_l5"],
           "m_season": b["m_season"], "m_last": b["m_last"], "gp": b["gp_cur"], "l10_min": b["l10_min"],
           "starter": b["starter_share"] >= 0.5, "stats": {}}
    for k in PROP_STATS:
        mu, var = x["mean"][k], max(x["var"][k], x["mean"][k] * 1.0001 + 1e-6)
        fair, over_upto, under_from, p_over = prop_line_info(mu, var)
        l10 = b["l10"][k]
        st = {"mu": mu, "var": var, "fair": fair, "over_upto": over_upto, "under_from": under_from,
              "l10": l10, "l10_avg": (sum(l10) / len(l10) if l10 else None),
              "avg_cur": b["avg_cur"][k], "avg_last": b["avg_last"][k],
              "hit_fair": (sum(1 for v in l10 if v > fair), len(l10)), "book": None}
        bk = props_book.get((x["pid"], k))
        if bk:
            line, o_, u_ = bk
            po = p_over(line)
            pu = 1 - po
            nv_o, nv_u = novig(o_, u_)
            # 50/50 blend with the book's no-vig price, then cautious margin
            bo = 0.5 * po + 0.5 * nv_o if nv_o is not None else po
            st["book"] = {"line": line, "over": o_, "under": u_, "p_over_model": po, "p_over": bo,
                          "hit": (sum(1 for v in l10 if v > line), len(l10))}
            lab = f"{short} {STAT_NAMES[k]}"
            ref = st["avg_cur"] if (b["gp_cur"] or 0) >= 3 else None
            hits = st["book"]["hit"]
            ex_o = {"proj": mu, "ref": ref, "ref_lbl": f"season avg ({b['gp_cur']} games)",
                    "hits": hits, "stat": STAT_NAMES[k].lower(), "minutes": x["min"]}
            ex_u = dict(ex_o, hits=(hits[1] - hits[0], hits[1]))
            st["mk_over"] = market(f"pr_{x['pid']}_{k}_O", "Player prop", f"{lab} over {line:g}", bo, 0, 1 - bo,
                                   CONFIG["buffer_props"], o_, line=line, mkt_p=nv_o, model_p=po,
                                   grade={"t": "prop", "pid": x["pid"], "stat": k, "side": "O", "line": line}, extra=ex_o)
            st["mk_under"] = market(f"pr_{x['pid']}_{k}_U", "Player prop", f"{lab} under {line:g}", 1 - bo, 0, bo,
                                    CONFIG["buffer_props"], u_, line=line, mkt_p=nv_u, model_p=1 - po,
                                    grade={"t": "prop", "pid": x["pid"], "stat": k, "side": "U", "line": line}, extra=ex_u)
        out["stats"][k] = st
    return out


def prop_ref(pr_gp, st):
    """What a book's line is likely anchored on: this season blended with last season until ~6 games in."""
    cur, last = st.get("avg_cur"), st.get("avg_last")
    gp = pr_gp or 0
    if cur is not None and last is not None:
        w = gp / (gp + 6.0)
        return w * cur + (1 - w) * last
    if cur is not None and gp >= 3:
        return cur
    return last if last is not None else st.get("l10_avg")


def head_to_head(c, h, a):
    out = []
    for gm in sorted(c.db.games.values(), key=lambda g: g["date"], reverse=True):
        if {gm["home"], gm["away"]} == {h, a} and gm["season"] >= c.cur - 1:
            out.append(gm)
    return out[:6]


# --------------------------------------------------------------------------
# How to bet each game, top bets, watch list
# --------------------------------------------------------------------------
def guide_for(c, ga):
    g = ga["g"]
    H, A = g["habbr"], g["aabbr"]
    lines = []
    mk = {m["key"]: m for m in ga["markets"]}
    if ga["sp_line"] is not None and mk["sp_H"].get("gap"):
        lines.append(("pass", f"Warning: the model alone ({fsp(H, -ga['mm'])}) is {abs(ga['mm'] + ga['sp_line']):.1f} points off "
                              f"the market ({fsp(H, ga['sp_line'])}). Gaps this big usually mean news the model can't see; "
                              "side bets here are not recommended."))
    if ga["tot_line"] is not None and mk["tot_O"].get("gap"):
        lines.append(("pass", f"Warning: the model total ({ga['mt']:.1f}) is {abs(ga['mt'] - ga['tot_line']):.1f} points off "
                              f"the market ({ga['tot_line']:g}); total bets here are not recommended."))
    priced = [m for m in ga["markets"] if m["book"] is not None]
    mm = ga["mm"]
    if ga["sp_line"] is not None:
        side = max((mk["sp_H"], mk["sp_A"]), key=lambda m: m["p"])
        mdl = "model " + fsp(H, -mm)
        if side["verdict"] == "value":
            lines.append(("bet", f"Side: {side['label']} at {fmt_am(side['book'])}. Good to {fmt_am(side['bet_at'])}; "
                                 f"{side['p']:.0%} to cover ({mdl})."))
        elif side["verdict"] == "lean":
            lines.append(("lean", f"Side: lean {side['label']} ({side['p']:.0%}, {mdl}). Only worth it at "
                                  f"{fmt_am(side['bet_at'])} or better."))
        else:
            lines.append(("pass", f"Side: no edge at {H} {ga['sp_line']:+g} ({mdl})."))
        ml_best = max((mk["ml_H"], mk["ml_A"]), key=lambda m: (m["ev_c"] if m["ev_c"] is not None else -9))
        if ml_best["verdict"] == "value":
            lines.append(("bet", f"Moneyline: {ml_best['label']} at {fmt_am(ml_best['book'])} "
                                 f"({ml_best['p']:.0%}, fair {fmt_am(ml_best['fair'])})."))
        else:
            fav = mk["ml_H"] if mk["ml_H"]["p"] >= 0.5 else mk["ml_A"]
            lines.append(("pass", f"Moneyline: {fav['label'].replace(' ML', '')} fair {fmt_am(fav['fair'])}; "
                                  f"bet it only at {fmt_am(fav['bet_at'])} or better."))
    else:
        th_h = spread_threshold(mm, CONFIG["w_model_margin"], CONFIG["sd_margin"], True)
        th_a = spread_threshold(mm, CONFIG["w_model_margin"], CONFIG["sd_margin"], False)
        lines.append(("watch", f"No line yet. Model {fsp(H, -mm)}. Bet {H} if the line is {fsp(H, -th_h)} or "
                               f"better; bet {A} if it is {fsp(A, th_a)} or better."))
    if ga["tot_line"] is not None:
        o, u = mk["tot_O"], mk["tot_U"]
        best = o if o["p"] >= u["p"] else u
        if best["verdict"] == "value":
            lines.append(("bet", f"Total: {best['label']} at {fmt_am(best['book'])} ({best['p']:.0%}; model total {ga['mt']:.1f})."))
        elif best["verdict"] == "lean":
            lines.append(("lean", f"Total: lean {best['label']} (model {ga['mt']:.1f}); thin edge."))
        else:
            lines.append(("pass", f"Total: pass at {ga['tot_line']:g} (model {ga['mt']:.1f})."))
    else:
        gap = CONFIG["sd_total"] * ninv(110 / 210 + CONFIG["buffer_total"]) / CONFIG["w_model_total"]
        lines.append(("watch", f"Total: model {ga['mt']:.1f}. Over only if the line is {ga['mt'] - gap:.1f} or lower; "
                               f"under only at {ga['mt'] + gap:.1f} or higher."))
    # props
    cands = []
    used_p = set()
    for pr in ga["props"]:
        for k in ("pts", "reb", "ast", "fg3m", "pra"):
            st = pr["stats"][k]
            if st.get("mk_over"):
                for mkx in (st["mk_over"], st["mk_under"]):
                    if mkx["verdict"] == "value":
                        cands.append((mkx["ev_c"] + 1, pr["pid"], f"{mkx['label']} at {fmt_am(mkx['book'])} (projection {st['mu']:.1f})"))
                continue
            ref = prop_ref(pr["gp"], st)
            if ref is None or pr["min"] < 20 or pr["pid"] in used_p:
                continue
            sd = math.sqrt(st["var"])
            z = (st["mu"] - ref) / max(sd, 0.5)
            if abs(z) >= 0.25 and abs(st["mu"] - ref) >= (2.0 if k in ("pts", "pra") else 0.8):
                lbl = "recent avg"
                if z > 0 and st["over_upto"] is not None:
                    cands.append((abs(z), pr["pid"], f"{pr['short']} {STAT_NAMES[k].lower()} over if the line is {st['over_upto']:g} or lower "
                                          f"(projection {st['mu']:.1f}, {lbl} {ref:.1f})"))
                elif z < 0 and st["under_from"] is not None:
                    cands.append((abs(z), pr["pid"], f"{pr['short']} {STAT_NAMES[k].lower()} under if the line is {st['under_from']:g} or higher "
                                          f"(projection {st['mu']:.1f}, {lbl} {ref:.1f})"))
    cands.sort(key=lambda x: -x[0])
    seen_p, n = set(), 0
    for _, pid, t in cands:
        if pid in seen_p:
            continue
        seen_p.add(pid)
        lines.append(("prop", "Prop: " + t + "."))
        n += 1
        if n >= 3:
            break
    # situational notes
    notes = []
    (rh, ra), (hb, ab) = ga["rest"], ga["b2b"]
    if hb:
        notes.append(f"{H} on the second night of a back-to-back")
    if ab:
        notes.append(f"{A} on the second night of a back-to-back")
    if rh and ra and not hb and not ab and abs(rh - ra) >= 2:
        notes.append(f"rest edge: {H if rh > ra else A} ({max(rh, ra)} days vs {min(rh, ra)})")
    for tid, ab_ in ((g["home"], H), (g["away"], A)):
        tot = ga["inj"][tid]["total"]
        if tot >= 1.5:
            notes.append(f"{ab_} missing about {tot:.1f} pts of value to injuries")
        elif tot <= -1.0:
            notes.append(f"{ab_} getting about {-tot:.1f} pts back from returning players")
    if notes:
        lines.append(("note", "Context: " + "; ".join(notes) + "."))
    return lines


def pick_top_bets(c, analyses):
    C = CONFIG
    cand = []
    gaps = []
    for ga in analyses:
        g = ga["g"]
        if g["state"] != "pre":
            continue
        ms = [m for m in ga["markets"] if m["book"] is not None]
        for pr in ga["props"]:
            for st in pr["stats"].values():
                for k in ("mk_over", "mk_under"):
                    if st.get(k):
                        ms.append(st[k])
        side_gap = abs(ga["mm"] + ga["sp_line"]) if ga["sp_line"] is not None else 0.0
        tot_gap = abs(ga["mt"] - ga["tot_line"]) if ga["tot_line"] is not None else 0.0
        for m in ms:
            if m["group"] in ("Spread", "Moneyline"):
                big = side_gap > C["max_gap_pts"]
            elif m["group"] == "Total":
                big = tot_gap > C["max_gap_pts_total"]
            else:
                big = m["model_p"] is not None and m["mkt_p"] is not None and abs(m["model_p"] - m["mkt_p"]) > C["max_market_gap"] + 0.05
            if big:
                if m["p"] > 0.5 or m["group"] not in ("Spread", "Moneyline", "Total"):
                    gaps.append((ga, m))
                continue
            if m["p"] < C["min_prob"] or m["ev"] is None or m["ev"] < C["min_ev_top"]:
                continue
            if m["book"] is not None and m["book"] < C["max_fav_top"]:
                continue
            kind = None
            if m["ev_c"] > 0:   # college: only bets that clear the Bet-at bar (the rule tested on 2025-26 prices)
                kind = "value"
            if kind:
                cand.append({"ga": ga, "m": m, "kind": kind})
    hp = sorted([x for x in cand if x["m"]["p"] >= C["high_prob_min"] and x["m"]["ev"] > 0],
                key=lambda x: (-x["m"]["p"], -x["m"]["ev"]))
    val = sorted([x for x in cand if x["kind"] == "value"], key=lambda x: -x["m"]["ev_c"])
    picked, per_game, used = [], {}, set()

    def ok(x):
        gid = x["ga"]["g"]["gid"]
        if x["m"]["group"] == "Player prop" and sum(1 for p in picked if p["m"]["group"] == "Player prop") >= C["max_props_top"]:
            return False
        key = x["m"]["key"]
        grp = {"ml": "side", "sp": "side"}.get(key.split("_")[0], key.split("_")[0]) + ("_" + key.split("_")[1] if key.startswith("pr_") else "")
        if (gid, grp) in used or per_game.get(gid, 0) >= C["max_per_game"]:
            return False
        if x["m"]["key"] in {p["m"]["key"] for p in picked if p["ga"]["g"]["gid"] == gid}:
            return False
        return True

    i = j = 0
    turn = 0
    while len(picked) < C["top_bets_max"] and (i < len(hp) or j < len(val)):
        src = hp if turn % 2 == 0 else val
        idx = i if turn % 2 == 0 else j
        while idx < len(src) and not ok(src[idx]):
            idx += 1
        if idx < len(src):
            x = dict(src[idx])
            x["tag"] = "High probability" if turn % 2 == 0 else "Value"
            if x["tag"] == "High probability" and x["m"]["ev_c"] > 0:
                x["tag"] = "High probability + value"
            gid = x["ga"]["g"]["gid"]
            key = x["m"]["key"]
            grp = {"ml": "side", "sp": "side"}.get(key.split("_")[0], key.split("_")[0]) + ("_" + key.split("_")[1] if key.startswith("pr_") else "")
            used.add((gid, grp))
            per_game[gid] = per_game.get(gid, 0) + 1
            picked.append(x)
            idx += 1
        if turn % 2 == 0:
            i = idx
        else:
            j = idx
        turn += 1
    picked.sort(key=lambda x: (x["ga"]["g"]["date"], -(x["m"]["ev_c"] or 0)))
    return picked, gaps


def watch_list(c, analyses):
    """Games later in the week without a line yet: where the model says to bet."""
    out = []
    for ga in analyses:
        if ga["sp_line"] is not None or ga["g"]["state"] != "pre":
            continue
        mm = ga["mm"]
        out.append({"ga": ga, "th_h": spread_threshold(mm, CONFIG["w_model_margin"], CONFIG["sd_margin"], True),
                    "th_a": spread_threshold(mm, CONFIG["w_model_margin"], CONFIG["sd_margin"], False)})
    return out


def price_check_props(c, analyses, limit=12):
    """Strong model prop spots without a fetched sportsbook price: what to look for at your book."""
    out = []
    for ga in analyses:
        if ga["g"]["state"] != "pre":
            continue
        for pr in ga["props"]:
            if pr["min"] < 24:
                continue
            for k in ("pts", "reb", "ast", "fg3m", "pra"):
                st = pr["stats"][k]
                ref = prop_ref(pr["gp"], st)
                if st.get("book") or ref is None:
                    continue
                sd = math.sqrt(st["var"])
                d = st["mu"] - ref
                z = d / max(sd, 0.5)
                if abs(z) < 0.3:
                    continue
                out.append({"ga": ga, "pr": pr, "k": k, "st": st, "z": z, "ref": ref})
    out.sort(key=lambda x: -abs(x["z"]))
    seen, res = set(), []
    for x in out:
        if x["pr"]["pid"] in seen:
            continue
        seen.add(x["pr"]["pid"])
        res.append(x)
        if len(res) >= limit:
            break
    return res


# --------------------------------------------------------------------------
# Track record: log pre-game probabilities, grade them once games finish
# --------------------------------------------------------------------------
def _grade_value(gr, gm, prow):
    t = gr["t"]
    margin = gm["hs"] - gm["as"]
    total = gm["hs"] + gm["as"]
    if t == "ml":
        return margin if gr["side"] == "H" else -margin
    if t == "sp":
        v = margin + gr["line"]
        return v if gr["side"] == "H" else -v
    if t == "tot":
        return (total - gr["line"]) if gr["side"] == "O" else (gr["line"] - total)
    if t == "tt":
        pts = gm["hs"] if gr["side"] == "H" else gm["as"]
        return (pts - gr["line"]) if gr["ou"] == "O" else (gr["line"] - pts)
    if t in ("1h_sp", "1h_tot", "1q_sp", "1q_tot"):
        hq, aq = gm.get("hq") or [None, None], gm.get("aq") or [None, None]
        if t.startswith("1h"):
            if None in hq or None in aq:
                return None
            h, a = hq[0] + hq[1], aq[0] + aq[1]
        else:
            if hq[0] is None or aq[0] is None:
                return None
            h, a = hq[0], aq[0]
        if t.endswith("sp"):
            v = (h - a) + gr["line"]
            return v if gr["side"] == "H" else -v
        return ((h + a) - gr["line"]) if gr["side"] == "O" else (gr["line"] - (h + a))
    if t == "prop":
        r = prow.get((gm["gid"], gr["pid"]))
        if not r or r["dnp"]:
            return None  # void: did not play
        v = stat_of(r, gr["stat"]) - gr["line"]
        return v if gr["side"] == "O" else -v
    return None


def update_log(c, analyses, top):
    path = os.path.join(DIRS["root"], "predictions.json")
    tpath = os.path.join(DIRS["root"], "top_bets.json")
    log_ = jload(path, {}) or {}
    tops = jload(tpath, {}) or {}
    ts = now_et().strftime("%Y-%m-%d %H:%M")
    pre_gids = set()
    for ga in analyses:
        g = ga["g"]
        if g["state"] != "pre":
            continue
        pre_gids.add(g["gid"])
        ms = list(ga["markets"])
        for pr in ga["props"]:
            for k, st in pr["stats"].items():
                if st.get("mk_over"):
                    ms += [st["mk_over"], st["mk_under"]]
        for m in ms:
            if not m.get("grade"):
                continue
            if m["est_line"] and m["group"] not in ("Spread", "Total"):
                continue
            log_[f"{g['gid']}|{m['key']}"] = {
                "date": g["date"], "game": f"{g['aabbr']} @ {g['habbr']}", "label": m["label"], "group": m["group"],
                "p": round(m["p"], 4), "pl": round(m["pl"], 4), "book": m["book"], "fair": m["fair"],
                "est": m["est_line"], "grade": m["grade"], "ts": ts}
    for k in [k for k, v in tops.items() if v.get("gid") in pre_gids]:
        del tops[k]
    for x in top:
        g, m = x["ga"]["g"], x["m"]
        tops[f"{g['gid']}|{m['key']}"] = {"gid": g["gid"], "date": g["date"], "game": f"{g['aabbr']} @ {g['habbr']}",
                                          "label": m["label"], "group": m["group"], "p": round(m["p"], 4),
                                          "book": m["book"], "tag": x["tag"], "grade": m["grade"], "ts": ts}
    # grade
    prow = {(r["gid"], r["pid"]): r for r in c.db.pbox if r["season"] == c.cur}
    for store in (log_, tops):
        for k, v in store.items():
            if "result" in v:
                continue
            gid = k.split("|")[0]
            gm = c.db.games.get(gid)
            if not gm:
                continue
            val = _grade_value(v["grade"], gm, prow)
            if val is None:
                if v["grade"]["t"] == "prop" and gm:
                    v["result"] = "void"
                continue
            v["result"] = "W" if val > 0 else ("L" if val < 0 else "P")
    jdump(log_, path)
    jdump(tops, tpath)
    return log_, tops


def export_picks(tops, path):
    """Every top bet in the same shape the other boards embed in their Track record scatter
    (read by run_all.py for the landing page)."""
    out = []
    for k, v in sorted(tops.items(), key=lambda kv: kv[1]["date"]):
        if v.get("book") is None:
            continue
        d = am_dec(v["book"])
        p = v["p"]
        r = v.get("result")
        pl = (d - 1) if r == "W" else (-1.0 if r == "L" else 0.0)
        tag = v.get("tag", "Value")
        out.append({"x": round((p * (d - 1) - (1 - p)) * 100, 2), "y": round(p, 4), "a": v["book"], "c": v["group"],
                    "t": "hp" if tag.startswith("High") else "va", "tn": "High probability" if tag.startswith("High") else "Value",
                    "gr": v.get("letter", "-"), "u": v.get("units", 0), "r": r if r in ("W", "L", "P") else "U",
                    "pl": round(pl, 3), "l": v["label"], "g": v["game"], "d": v["date"]})
    jdump(out, path)
    return out


def summarize_log(log_, tops):
    def agg(items, priced_only=False):
        n = w = l = p = 0
        units = staked = brier = 0.0
        for v in items:
            r = v.get("result")
            if r not in ("W", "L", "P"):
                continue
            if priced_only and v.get("book") is None:
                continue
            n += 1
            if r == "W":
                w += 1
            elif r == "L":
                l += 1
            else:
                p += 1
            if r != "P":
                brier += (v["p"] / max(1e-9, v["p"] + v.get("pl", 1 - v["p"])) - (1 if r == "W" else 0)) ** 2
            if v.get("book") is not None:
                staked += 1
                units += (am_dec(v["book"]) - 1) if r == "W" else (-1 if r == "L" else 0)
        return {"n": n, "w": w, "l": l, "p": p, "units": units, "staked": staked,
                "roi": units / staked if staked else None, "brier": brier / max(1, w + l)}
    groups = {}
    for v in log_.values():
        if v["p"] < 0.5:  # count each market once, from the side the model favoured
            continue
        groups.setdefault(v["group"], []).append(v)
    rows = [(g, agg(items)) for g, items in sorted(groups.items())]
    value_bets = [v for v in log_.values() if v.get("book") is not None and v["p"] - 0.025 > 1 / am_dec(v["book"]) * 1.0]
    return {"groups": rows, "top": agg(tops.values()), "top_items": sorted(tops.values(), key=lambda v: v["date"], reverse=True),
            "value": agg(value_bets)}


# --------------------------------------------------------------------------
# HTML
# --------------------------------------------------------------------------
CSS = r"""
:root{--bg:#F1EFF2;--surface:#FFFFFF;--sunk:#F7F5F8;--ink:#1D1820;--muted:#625A68;--line:#DDD7E0;
--accent:#7A1F3D;--accent-soft:#F4E3E9;--value:#127A5B;--value-soft:#DDF1E9;--lean:#9A6A0C;--lean-soft:#F7ECD3;
--avoid:#B23A30;--avoid-soft:#F6E0DD;--focus:#7A1F3D;color-scheme:light}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){--bg:#141016;--surface:#1E1822;--sunk:#18131B;--ink:#EEE9F0;
--muted:#A79FAD;--line:#352C3A;--accent:#E58FAA;--accent-soft:#4A2433;--value:#46C796;--value-soft:#163A2F;--lean:#E3AE45;
--lean-soft:#3B3020;--avoid:#EE7366;--avoid-soft:#43211F;--focus:#E58FAA;color-scheme:dark}}
:root[data-theme="dark"]{--bg:#141016;--surface:#1E1822;--sunk:#18131B;--ink:#EEE9F0;--muted:#98A2B3;--line:#2A3446;
--accent:#8EA2F2;--accent-soft:#22305A;--value:#46C796;--value-soft:#163A2F;--lean:#E3AE45;--lean-soft:#3B3020;
--avoid:#EE7366;--avoid-soft:#43211F;--focus:#E58FAA;color-scheme:dark}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.5 "Barlow",system-ui,-apple-system,"Segoe UI",sans-serif}
.num,.cond{font-family:"Barlow Condensed","Arial Narrow",system-ui,sans-serif;font-variant-numeric:tabular-nums}
a{color:var(--accent)}
:focus-visible{outline:2px solid var(--focus);outline-offset:2px}
.wrap{max-width:1180px;margin:0 auto;padding:0 16px}
header.top{padding:22px 0 10px}
.brand{display:flex;flex-wrap:wrap;align-items:baseline;gap:6px 18px}
.brand h1{font:700 40px/1 "Barlow Condensed",system-ui,sans-serif;margin:0;letter-spacing:.2px}
.brand .meta{color:var(--muted);font-size:14px}
.alerts{margin:10px 0 0;display:grid;gap:6px}
.alert{background:var(--lean-soft);border-left:3px solid var(--lean);padding:8px 12px;font-size:14px;border-radius:2px}
nav.tabs{position:sticky;top:0;z-index:5;background:var(--bg);border-bottom:1px solid var(--line);margin-top:12px}
nav.tabs .wrap{display:flex;gap:2px;overflow-x:auto;scrollbar-width:none}
nav.tabs button{font:600 17px/1 "Barlow Condensed",system-ui,sans-serif;background:none;border:0;color:var(--muted);
padding:13px 12px 11px;border-bottom:3px solid transparent;cursor:pointer;white-space:nowrap}
nav.tabs button[aria-selected="true"]{color:var(--ink);border-bottom-color:var(--accent)}
section.tab{display:none;padding:18px 0 48px}section.tab.on{display:block}
h2{font:700 26px/1.1 "Barlow Condensed",system-ui,sans-serif;margin:0 0 6px}
h3{font:600 20px/1.15 "Barlow Condensed",system-ui,sans-serif;margin:22px 0 8px}
h4{font:600 16px/1.2 "Barlow Condensed",system-ui,sans-serif;margin:14px 0 6px;color:var(--muted)}
p.lede{color:var(--muted);max-width:72ch;margin:0 0 14px}
.panel{background:var(--surface);border:1px solid var(--line);border-radius:6px}
/* week strip */
.days{display:flex;gap:6px;overflow-x:auto;padding:2px 0 12px;scrollbar-width:thin}
.days button{flex:0 0 auto;min-width:74px;background:var(--surface);border:1px solid var(--line);border-radius:6px;
padding:6px 10px;text-align:left;cursor:pointer;color:var(--ink)}
.days button b{display:block;font:600 17px/1.1 "Barlow Condensed",system-ui,sans-serif}
.days button span{font-size:12px;color:var(--muted)}
.days button[aria-pressed="true"]{border-color:var(--accent);box-shadow:inset 0 -3px 0 var(--accent)}
/* top bets */
.record{display:flex;flex-wrap:wrap;gap:8px 24px;margin:0 0 14px;font-size:14px;color:var(--muted)}
.record b{color:var(--ink);font:600 18px/1 "Barlow Condensed",system-ui,sans-serif}
ol.bets{list-style:none;margin:0;padding:0;display:grid;gap:10px}
ol.bets>li{display:grid;grid-template-columns:44px 1fr;gap:0 14px;padding:14px 16px}
.rank{font:700 34px/1 "Barlow Condensed",system-ui,sans-serif;color:var(--accent);text-align:right}
.bet-h{display:flex;flex-wrap:wrap;align-items:baseline;gap:4px 12px}
.bet-h .pick{font:700 23px/1.1 "Barlow Condensed",system-ui,sans-serif}
.bet-h .price{font:600 23px/1.1 "Barlow Condensed",system-ui,sans-serif}
.bet-sub{color:var(--muted);font-size:14px;margin:2px 0 8px}
.tag{display:inline-block;font-size:12.5px;font-weight:600;padding:1px 8px;border-radius:10px;background:var(--accent-soft);color:var(--accent)}
.tag.value{background:var(--value-soft);color:var(--value)}.tag.lean{background:var(--lean-soft);color:var(--lean)}
.tag.avoid{background:var(--avoid-soft);color:var(--avoid)}.tag.muted{background:var(--sunk);color:var(--muted)}
.facts{display:flex;flex-wrap:wrap;gap:4px 18px;font-size:14px;margin-top:8px}
.facts span{color:var(--muted)}.facts b{color:var(--ink);font-weight:600}
.why{font-size:14px;margin:8px 0 0;max-width:80ch}
/* price bar: the signature element */
.pbar{position:relative;margin:6px 0 2px;max-width:520px}
.pbar .track{display:flex;height:10px;border-radius:5px;overflow:hidden}
.pbar .z{height:100%}.pbar .zv{background:var(--value)}.pbar .zl{background:var(--lean)}.pbar .za{background:var(--avoid);opacity:.75}
.pbar .mark{position:absolute;top:-5px;width:3px;height:20px;background:var(--ink);border-radius:2px;transform:translateX(-1px)}
.pbar .mlab{position:absolute;top:-22px;transform:translateX(-50%);font:600 13px/1 "Barlow Condensed",system-ui,sans-serif;white-space:nowrap}
.pbar .ticks{position:relative;height:18px;font-size:12px;color:var(--muted)}
.pbar .ticks span{position:absolute;top:2px;transform:translateX(-50%);white-space:nowrap}
.pbar.withmark{margin-top:24px}
/* games */
.game{margin:0 0 10px}
.game>summary{list-style:none;cursor:pointer;padding:12px 14px;display:grid;grid-template-columns:minmax(0,1.4fr) minmax(0,1fr) auto;gap:6px 16px;align-items:center}
.game>summary::-webkit-details-marker{display:none}
.match{display:grid;gap:2px}
.tm{display:flex;align-items:baseline;gap:8px;min-width:0}
.tm .ab{font:700 21px/1.1 "Barlow Condensed",system-ui,sans-serif;width:48px;flex:0 0 auto}
.tm .nm{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.tm .rec{color:var(--muted);font-size:13px;white-space:nowrap}
.tm .proj{margin-left:auto;font:600 19px/1 "Barlow Condensed",system-ui,sans-serif}
.sline{font-size:14px;color:var(--muted);display:grid;gap:2px}
.sline b{color:var(--ink);font-weight:600}
.best{justify-self:end;text-align:right;font-size:14px}
.best .chip{display:inline-block;font:600 16px/1.2 "Barlow Condensed",system-ui,sans-serif;padding:3px 9px;border-radius:4px;background:var(--value-soft);color:var(--value)}
.best .chip.none{background:var(--sunk);color:var(--muted)}
.gbody{border-top:1px solid var(--line);padding:4px 14px 16px}
.guide{list-style:none;margin:12px 0 4px;padding:0;display:grid;gap:5px;max-width:86ch}
.guide li{padding-left:14px;position:relative;font-size:14.5px}
.guide li::before{content:"";position:absolute;left:0;top:.55em;width:7px;height:7px;border-radius:50%;background:var(--muted)}
.guide li.bet::before{background:var(--value)}.guide li.lean::before{background:var(--lean)}.guide li.pass::before{background:var(--avoid)}
.guide li.prop::before{background:var(--accent)}.guide li.watch::before{background:var(--accent)}
.cols{display:grid;grid-template-columns:1fr 1fr;gap:4px 22px}
.tbl-wrap{overflow-x:auto;-webkit-overflow-scrolling:touch}
table{border-collapse:collapse;width:100%;font-size:13.5px}
th,td{padding:5px 7px;text-align:right;white-space:nowrap;border-bottom:1px solid var(--line)}
th{font-weight:600;color:var(--muted);font-size:12.5px;position:sticky;top:0;background:var(--surface)}
td:first-child,th:first-child{text-align:left}
td.l,th.l{text-align:left}
tr.sub td{color:var(--muted)}
table.sortable th{cursor:pointer}
td .v{color:var(--value);font-weight:600}td .le{color:var(--lean);font-weight:600}td .a{color:var(--avoid);font-weight:600}
.dim{color:var(--muted)}
input.bk,input.ln{width:62px;font:inherit;font-size:13.5px;padding:2px 5px;border:1px solid var(--line);border-radius:4px;background:var(--sunk);color:var(--ink);text-align:right}
.out{display:inline-block;min-width:74px;text-align:left}
.split{display:grid;grid-template-columns:repeat(auto-fit,minmax(260px,1fr));gap:12px}
.mini{font-size:13.5px}
.mini .r{display:flex;justify-content:space-between;gap:10px;border-bottom:1px solid var(--line);padding:3px 0}
.mini .r span:first-child{color:var(--muted)}
.form{display:flex;gap:3px;flex-wrap:wrap}
.form i{font-style:normal;font:600 12px/18px "Barlow Condensed",system-ui,sans-serif;width:20px;text-align:center;border-radius:3px;background:var(--sunk)}
.form i.w{background:var(--value-soft);color:var(--value)}.form i.l{background:var(--avoid-soft);color:var(--avoid)}
.legend{font-size:13px;color:var(--muted);margin:6px 0 0}
.controls{display:flex;flex-wrap:wrap;gap:8px 14px;align-items:center;margin:0 0 10px}
.controls select,.controls input{font:inherit;padding:5px 8px;border:1px solid var(--line);border-radius:4px;background:var(--surface);color:var(--ink)}
.calc{padding:12px 14px;margin:0 0 12px;display:none}
.calc.on{display:block}
.note{font-size:13.5px;color:var(--muted);max-width:80ch}
.how p{max-width:76ch}
.empty{padding:16px;color:var(--muted)}
.tm .rk{font:600 12px/1 "Barlow Condensed",system-ui,sans-serif;color:var(--accent);width:16px;text-align:right;flex:0 0 auto}
.tm .ab{width:auto;min-width:52px;padding-right:6px}
details.conf{margin:0 0 8px}details.conf>summary{cursor:pointer;padding:10px 14px}details.conf .tbl-wrap{padding:0 8px 8px}
.daygroup>h3{position:sticky;top:44px;background:var(--bg);padding:6px 0;z-index:2}
details.watch>summary{cursor:pointer;list-style:none}details.watch>summary::-webkit-details-marker{display:none}
details.watch>summary h3::before{content:"\25B8  ";color:var(--muted)}details.watch[open]>summary h3::before{content:"\25BE  "}
.themebtn{margin-left:auto;background:none;border:1px solid var(--line);border-radius:4px;color:var(--muted);font:inherit;font-size:13px;padding:3px 8px;cursor:pointer}
@media (max-width:760px){
 .game>summary{grid-template-columns:1fr;}
 .best{justify-self:start;text-align:left}
 .cols{grid-template-columns:1fr}
 .brand h1{font-size:34px}
 ol.bets>li{grid-template-columns:30px 1fr;padding:12px}
 .rank{font-size:26px}
 .pbar .ticks{display:flex;gap:14px;height:auto;margin-top:4px}
 .pbar .ticks span{position:static;transform:none}
}
@media (prefers-reduced-motion:reduce){*{scroll-behavior:auto!important}}
"""

JS = r"""
(function(){
const $=(s,r=document)=>r.querySelector(s), $$=(s,r=document)=>Array.from(r.querySelectorAll(s));
function amDec(a){return a>0?1+a/100:1+100/Math.abs(a)}
function parseAm(t){t=String(t||'').trim().toUpperCase().replace('−','-');if(!t)return null;if(t==='EVEN'||t==='EV')return 100;
 let x=parseFloat(t.replace('+',''));if(!isFinite(x))return null;if(Math.abs(x)>=100)return Math.round(x);
 if(x>1.01&&x<50)return x>=2?Math.round((x-1)*100):Math.round(-100/(x-1));return null}
function fmtAm(a){if(a==null||!isFinite(a))return '–';a=Math.round(a);return a>0?'+'+a:String(a)}
function fairAm(pw,pl){if(pw<=0.0005)return null;const d=1+pl/pw;return d>=2?Math.round((d-1)*100):Math.round(-100/(d-1))}
function erf(x){const s=Math.sign(x);x=Math.abs(x);const t=1/(1+0.3275911*x);
 const y=1-(((((1.061405429*t-1.453152027)*t)+1.421413741)*t-0.284496736)*t+0.254829592)*t*Math.exp(-x*x);return s*y}
function ncdf(x){return 0.5*(1+erf(x/Math.SQRT2))}
function lineProbs(mu,sd,L){if(Math.abs(L-Math.round(L))<1e-9){const hi=1-ncdf((L+0.5-mu)/sd),lo=ncdf((L-0.5-mu)/sd);return[hi,Math.max(0,1-hi-lo),lo]}
 const hi=1-ncdf((L-mu)/sd);return[hi,0,1-hi]}
function nbOver(mu,v,L){const k=Math.floor(L);if(k<0)return 1;let c=0;
 if(v<=mu*1.0001){let p=Math.exp(-mu);for(let i=0;i<=k;i++){c+=p;p*=mu/(i+1)}}
 else{const p=mu/v,r=mu*p/(1-p);let pk=Math.pow(p,r);for(let i=0;i<=k;i++){c+=pk;pk*=(i+r)/(i+1)*(1-p)}}
 return Math.max(0,1-Math.min(1,c))}
function verdict(pw,pl,buf,am){const d=amDec(am),ev=pw*(d-1)-pl,evc=Math.max(0.001,pw-buf)*(d-1)-Math.min(0.999,pl+buf);
 return {ev,evc,tag:evc>0?'value':(ev>0?'lean':'avoid'),txt:evc>0?'Value':(ev>0?'Lean':'Avoid')}}
function show(out,v){out.innerHTML=v?`<span class="${v.tag==='value'?'v':v.tag==='lean'?'le':'a'}">${v.txt} ${(v.ev*100>=0?'+':'')+(v.ev*100).toFixed(1)}%</span>`:''}
// tabs
const tabs=$$('nav.tabs button');
function openTab(id,push){tabs.forEach(b=>b.setAttribute('aria-selected',b.dataset.tab===id));
 $$('section.tab').forEach(s=>s.classList.toggle('on',s.id===id));if(push)history.replaceState(null,'','#'+id)}
tabs.forEach(b=>b.addEventListener('click',()=>openTab(b.dataset.tab,true)));
const h=location.hash.slice(1);if(h&&$('#'+h)&&$('#'+h).classList.contains('tab'))openTab(h,false);
// theme
const tb=$('#themebtn');try{const t=localStorage.getItem('cbbedge-theme');if(t)document.documentElement.dataset.theme=t}catch(e){}
tb&&tb.addEventListener('click',()=>{const cur=document.documentElement.dataset.theme||(matchMedia('(prefers-color-scheme: dark)').matches?'dark':'light');
 const n=cur==='dark'?'light':'dark';document.documentElement.dataset.theme=n;try{localStorage.setItem('cbbedge-theme',n)}catch(e){}});
// games: day buttons, search and filters
let curDay=(($('.days button[aria-pressed="true"]')||{}).dataset||{}).day||'all';
function applyFilters(){const q=(($('#gSearch')||{}).value||'').trim().toLowerCase(),show=($('#gShow')||{}).value||'all',cf=($('#gConf')||{}).value||'';
 let n=0;$$('.daygroup').forEach(g=>{let k=0;const dayOn=curDay==='all'||g.dataset.day===curDay||q.length>1;
  $$('details.game',g).forEach(d=>{const ok=dayOn&&(!q||d.dataset.q.includes(q))&&(show==='all'||(show==='line'&&d.dataset.line==='1')||
   (show==='val'&&d.dataset.val==='1')||(show==='rk'&&d.dataset.rk==='1'))&&(!cf||d.dataset.conf.split(' ').includes(cf));d.hidden=!ok;if(ok)k++});
  g.hidden=!dayOn||k===0;n+=k});
 const c=$('#gCount');if(c)c.textContent=n+' game'+(n===1?'':'s');const none=$('#gNone');if(none)none.hidden=n>0}
$$('.days button').forEach(b=>b.addEventListener('click',()=>{$$('.days button').forEach(x=>x.setAttribute('aria-pressed',x===b));curDay=b.dataset.day;applyFilters()}));
['#gSearch','#gShow','#gConf'].forEach(id=>{const e=$(id);if(e){e.addEventListener('input',applyFilters);e.addEventListener('change',applyFilters)}});
applyFilters();
// game details are drawn from GAMES / TEAMS when a game is opened
const G=window.GAMES||{},TM=window.TEAMS||{},SR=window.STATROWS||[];
function esc(s){return String(s??'').replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]))}
function pctS(x){return x==null?'–':Math.round(x*100)+'%'}
function f1g(x,d=1){return x==null?'–':(+x).toFixed(d)}
function ordS(n){if(n==null)return '–';const s=(n%100>=11&&n%100<=13)?'th':({1:'st',2:'nd',3:'rd'}[n%10]||'th');return n+s}
const MKHEAD='<tr><th class="l">Bet</th><th class="l">Line</th><th>Our %</th><th>Market %</th><th>Fair</th><th>Bet at</th><th>Your price</th><th class="l">Verdict</th></tr>';
function mkTable(list){return '<div class="tbl-wrap"><table><thead>'+MKHEAD+'</thead><tbody>'+list.map(m=>{const [lab,line,p,pl,mp,fair,bat,book,buf,mu,sd,kind,side,est]=m;
 let at=`data-p="${p}" data-pl="${pl}" data-buf="${buf}"`,ln='';
 if(mu!=null){at+=` data-mu="${mu}" data-sd="${sd}" data-kind="${kind}" data-side="${side}"`;ln=`<input class="ln" inputmode="decimal" aria-label="Line for ${esc(lab)}" value="${line}">`+(est?' <span class="dim" title="Estimated line: type your book\'s line">est.</span>':'')}
 return `<tr ${at}><td class="l">${esc(lab)}</td><td class="l">${ln}</td><td class="pc">${pctS(p)}</td><td class="dim">${pctS(mp)}</td><td class="fa">${fmtAm(fair)}</td><td class="ba">${fmtAm(bat)}</td><td><input class="bk" aria-label="Your price for ${esc(lab)}" value="${book==null?'':fmtAm(book)}" placeholder="-110"></td><td class="l"><span class="out"></span></td></tr>`}).join('')+'</tbody></table></div>'}
function teamName(t){const x=TM[t]||{};return (x.rk?'#'+x.rk+' ':'')+(x.nm||x.ab||t)}
function drawGame(det){const g=G[det.dataset.gid];const box=$('.gbody',det);if(!g||!box||box.dataset.done)return;box.dataset.done='1';
 const A=TM[g.a]||{},H=TM[g.h]||{};let o='';
 o+='<ul class="guide">'+g.gd.map(x=>`<li class="${x[0]}">${esc(x[1])}</li>`).join('')+'</ul>';
 if(g.note)o+=`<p class="note">${esc(g.note)}${g.venue?' · '+esc(g.venue):''}</p>`;else if(g.venue)o+=`<p class="note">${esc(g.venue)}</p>`;
 const main=g.mk.filter(m=>['Moneyline','Spread','Total'].includes(m[14])),der=g.mk.filter(m=>!['Moneyline','Spread','Total'].includes(m[14]));
 o+='<h3>Betting board</h3>'+mkTable(main)+'<details><summary class="dim" style="cursor:pointer;margin:8px 0">Team totals and 1st half (estimated lines: type your book\'s line)</summary>'+mkTable(der)+'</details>';
 o+='<p class="legend">Our % blends the model with the market when a line is posted. Fair is the break-even price; Bet at adds a safety margin. Type your book\'s price to see the expected return.</p>';
 o+='<h3>Who\'s missing</h3><div class="cols">';
 for(const t of [g.a,g.h]){const x=TM[t]||{},rows=g.inj[t]||[];
  o+=`<div><h4>${esc(x.ab||'')}</h4>`+(x.d1?(rows.length?'<div class="tbl-wrap"><table><thead><tr><th class="l">Player</th><th class="l">Status</th><th>Min</th><th>Pts</th><th title="Margin points per game over a replacement player">Value</th><th>Plays</th></tr></thead><tbody>'+
   rows.map(r=>`<tr><td class="l">${esc(r[0])}</td><td class="l"><span class="tag ${r[6]<=0.25?'avoid':'lean'}">${esc(r[1])}</span></td><td>${f1g(r[3])}</td><td>${f1g(r[4])}</td><td>${f1g(r[5])}</td><td>${pctS(r[6])}</td></tr>`).join('')+'</tbody></table></div>':
   '<p class="note">No rotation player has missed a recent game.</p>'):'<p class="note">Non-Division I team: no data.</p>')+'</div>'}
 o+='</div>';
 o+='<h3>Minutes and player projections</h3><p class="note">Each cell: projection, then over ≤ / under ≥ (the lines where a -110 bet has an edge after the safety margin). Minutes: projected, then last 5 / season below.</p><div class="cols">';
 for(const t of [g.a,g.h]){const x=TM[t]||{},rows=g.pl[t]||[];
  o+=`<div><h4>${esc(x.ab||'')}</h4><div class="tbl-wrap"><table><thead><tr><th class="l">Player</th><th>Min</th><th>Pts</th><th>Reb</th><th>Ast</th><th>3PM</th><th>PRA</th></tr></thead><tbody>`+
   (rows.map(r=>`<tr><td class="l">${esc(r[0])}${r[10]<0.99?` <span class="tag ${r[10]<=0.25?'avoid':'lean'}">${pctS(r[10])} to play</span>`:''}</td><td><b>${f1g(r[1],0)}</b><br><span class="dim">${f1g(r[2],0)} / ${f1g(r[3],0)}</span></td>`+
    [4,5,6,7,8].map(i=>`<td>${f1g(r[i][0])}<br><span class="dim">${r[i][1]??'–'} / ${r[i][2]??'–'}</span></td>`).join('')+'</tr>').join('')||'<tr><td class="l" colspan="7">No player data.</td></tr>')+'</tbody></table></div></div>'}
 o+='</div><h3>Form and trends</h3><div class="split">';
 g.rest.forEach((r,i)=>{});
 [[g.a,g.rest[1]],[g.h,g.rest[0]]].forEach(([t,rest])=>{const x=TM[t]||{};if(!x.d1){o+=`<div class="mini panel" style="padding:10px 12px"><h4 style="margin-top:0">${esc(x.nm||'')}</h4><p class="note">Non-Division I team.</p></div>`;return}
  const restT=rest==null?'first game':(rest===1?'played yesterday':(rest-1)+' day'+(rest>2?'s':'')+' of rest');
  const form=(x.last||[]).map(r=>`<i class="${r[3]>r[4]?'w':'l'}" title="${r[0]} ${['vs','vs (neutral)','at'][r[2]]} ${esc(r[1])} ${r[3]}-${r[4]}">${r[3]>r[4]?'W':'L'}</i>`).join('');
  o+=`<div class="mini panel" style="padding:10px 12px"><h4 style="margin-top:0">${esc(teamName(t))}</h4><div class="form">${form||'<span class=dim>No games yet</span>'}</div>`+
   `<div class="r"><span>Record</span><span>${x.wl} (${esc(x.cf)} ${x.cwl}, ${ordS(x.cr)})</span></div>`+
   `<div class="r"><span>Home / road / neutral</span><span>${x.hm} / ${x.rd} / ${x.nu}</span></div>`+
   `<div class="r"><span>Against the spread</span><span>${x.ats}</span></div><div class="r"><span>Over / under</span><span>${x.ou}</span></div>`+
   `<div class="r"><span>Streak</span><span>${x.sk||'–'}</span></div><div class="r"><span>Rest</span><span>${restT}</span></div>`+
   `<div class="r"><span>Model rating (rank of ${Object.values(TM).filter(v=>v.d1).length>300?'365':'D1'})</span><span>${x.net>=0?'+':''}${f1g(x.net)} (${ordS(x.pw)})</span></div>`+
   `<div class="r"><span>Roster change vs last season</span><span>${x.sh>=0?'+':''}${f1g(x.sh)} pts</span></div>`+
   (x.last||[]).slice().reverse().map(r=>`<div class="r"><span>${r[0].slice(5)} ${['vs','vs','at'][r[2]]} ${esc(r[1])}${r[2]===1?' (N)':''}</span><span>${r[3]>r[4]?'W':'L'} ${r[3]}-${r[4]}${r[5]?(r[5]==='W'?' (cover)':r[5]==='L'?' (no cover)':' (push)'):''}</span></div>`).join('')+'</div>'});
 o+='</div>';
 if(g.h2h.length)o+='<h4>Head to head (this season and last)</h4><div class="mini" style="max-width:520px">'+g.h2h.map(r=>`<div class="r"><span>${r[0]}</span><span>${esc(r[1])} ${r[2]} @ ${esc(r[3])} ${r[4]}</span></div>`).join('')+'</div>';
 if(A.d1||H.d1){o+=`<h3>Stats and ranks (of 365)</h3><div class="tbl-wrap" style="max-width:660px"><table><thead><tr><th class="l">This season</th><th>${esc(A.ab||'')}</th><th>${esc(H.ab||'')}</th></tr></thead><tbody>`+
  SR.map((lab,i)=>{const c=(x)=>{const v=(x.st||[])[i];if(!v||v[0]==null)return '–';const val=(lab[1]==='+1'&&v[0]>=0?'+':'')+(+v[0]).toFixed(1);return v[1]?`${val} <span class="dim">(${ordS(v[1])})</span>`:val};
   return `<tr><td class="l">${esc(lab[0])}</td><td>${c(A)}</td><td>${c(H)}</td></tr>`}).join('')+'</tbody></table></div>'}
 box.innerHTML=o;
 $$('tr[data-p]',box).forEach(tr=>{rowCalc(tr);$$('input',tr).forEach(i=>i.addEventListener('input',()=>rowCalc(tr)))});
 $$('details',box).forEach(d=>{})}
$$('details.game').forEach(d=>d.addEventListener('toggle',()=>{if(d.open)drawGame(d)}));
// price inputs on market rows
function rowCalc(tr){const bk=$('input.bk',tr),ln=$('input.ln',tr),out=$('.out',tr);if(!bk)return;
 const am=parseAm(bk.value);let pw=+tr.dataset.p,pl=+tr.dataset.pl;const buf=+tr.dataset.buf;
 if(ln&&tr.dataset.mu){const L=parseFloat(ln.value);if(isFinite(L)){const mu=+tr.dataset.mu,sd=+tr.dataset.sd,side=tr.dataset.side;
  let q;if(tr.dataset.kind==='margin'){q=lineProbs(mu,sd,-L);pw=q[0];pl=q[2]}else{q=lineProbs(mu,sd,L);if(side==='O'){pw=q[0];pl=q[2]}else{pw=q[2];pl=q[0]}}
  $('.pc',tr).textContent=(pw*100).toFixed(0)+'%';$('.fa',tr).textContent=fmtAm(fairAm(pw,pl));
  $('.ba',tr).textContent=fmtAm(fairAm(Math.max(0.001,pw-buf),Math.min(0.999,pl+buf)))}}
 show(out,am==null?null:verdict(pw,pl,buf,am))}
$$('tr[data-p]').forEach(tr=>{rowCalc(tr);$$('input',tr).forEach(i=>i.addEventListener('input',()=>rowCalc(tr)))});
const hg=location.hash.match(/^#g(\d+)$/);if(hg){const d=$('details.game[data-gid="'+hg[1]+'"]');if(d){openTab('games',false);$$('.days button').forEach(x=>x.setAttribute('aria-pressed',x.dataset.day===d.dataset.day));curDay=d.dataset.day;applyFilters();d.open=true;d.scrollIntoView()}}
// sortable tables
$$('table.sortable').forEach(t=>{$$('th',t).forEach((th,i)=>th.addEventListener('click',()=>{const tb=t.tBodies[0];
 const rows=Array.from(tb.rows);const asc=th.dataset.asc!=='1';$$('th',t).forEach(x=>delete x.dataset.asc);th.dataset.asc=asc?'1':'0';
 rows.sort((a,b)=>{const x=a.cells[i].dataset.s??a.cells[i].textContent,y=b.cells[i].dataset.s??b.cells[i].textContent;
  const nx=parseFloat(x),ny=parseFloat(y);const c=(isFinite(nx)&&isFinite(ny))?nx-ny:String(x).localeCompare(String(y));return asc?c:-c});
 rows.forEach(r=>tb.appendChild(r))}))});
// props tab
const P=window.PROPS||[];const S=window.STATNAMES||{};
const selD=$('#pDay'),selS=$('#pStat'),q=$('#pSearch'),body=$('#pBody'),calc=$('#pCalc');
function f1(x){return x==null?'–':(+x).toFixed(1)}
function renderProps(){if(!body)return;const d=selD.value,k=selS.value,s=(q.value||'').toLowerCase();
 const rows=P.filter(r=>(d==='all'||r.d===d)&&(!s||r.n.toLowerCase().includes(s)||r.t.toLowerCase().includes(s)||r.o.toLowerCase().includes(s)));
 rows.sort((a,b)=>b.st[k][0]-a.st[k][0]);const more=$('#pMore');if(more)more.textContent=rows.length>250?`Showing the top 250 of ${rows.length}. Search for a player or team to see the rest.`:'';
 body.innerHTML=rows.slice(0,250).map((r,i)=>{const x=r.st[k];const bk=x[8]!=null?`${x[8]} <span class="dim">${fmtAm(x[9])}/${fmtAm(x[10])}</span>`:'<span class="dim">–</span>';
  const hit=x[6]!=null?`${x[6]}/${x[7]}`:'–';const st=r.pp<1?` <span class="tag ${r.pp<=0.25?'avoid':'lean'}">${r.status}</span>`:'';
  return `<tr data-i="${P.indexOf(r)}" tabindex="0"><td class="l">${r.n}${st}</td><td class="l">${r.t} ${r.h?'vs':'@'} ${r.o}</td><td class="l">${r.dl}</td>
  <td data-s="${r.min}">${f1(r.min)}</td><td>${f1(r.l5)}</td><td data-s="${x[0]}"><b>${f1(x[0])}</b></td><td>${x[2]}</td>
  <td>${x[3]??'–'}</td><td>${x[4]??'–'}</td><td>${f1(x[5])}</td><td>${hit}</td><td>${f1(x[11])}</td><td>${bk}</td></tr>`}).join('')||
  '<tr><td colspan="13" class="l dim">No players match. Clear the search or pick another day.</td></tr>';
 $$('tr[data-i]',body).forEach(tr=>{const go=()=>openCalc(P[+tr.dataset.i]);tr.addEventListener('click',go);tr.addEventListener('keydown',e=>{if(e.key==='Enter')go()})})}
let cur=null;
function openCalc(r){cur=r;calc.classList.add('on');const k=selS.value,x=r.st[k];$('#cName').textContent=`${r.n}: ${S[k]}`;
 $('#cInfo').textContent=`Projection ${f1(x[0])} in ${f1(r.min)} minutes. Fair line ${x[2]}.`;
 $('#cLine').value=x[8]!=null?x[8]:x[2];$('#cOver').value=x[9]!=null?fmtAm(x[9]):'-110';$('#cUnder').value=x[10]!=null?fmtAm(x[10]):'-110';runCalc();
 calc.scrollIntoView({block:'nearest'})}
function runCalc(){if(!cur)return;const k=selS.value,x=cur.st[k];const L=parseFloat($('#cLine').value);if(!isFinite(L))return;
 const po=nbOver(x[0],x[1],L),pu=1-po,buf=window.PROPBUF||0.04;
 const o=parseAm($('#cOver').value),u=parseAm($('#cUnder').value);
 $('#cProb').innerHTML=`Over ${(po*100).toFixed(0)}% <span class="dim">(fair ${fmtAm(fairAm(po,pu))}, bet at ${fmtAm(fairAm(Math.max(.001,po-buf),Math.min(.999,pu+buf)))})</span><br>Under ${(pu*100).toFixed(0)}% <span class="dim">(fair ${fmtAm(fairAm(pu,po))}, bet at ${fmtAm(fairAm(Math.max(.001,pu-buf),Math.min(.999,po+buf)))})</span>`;
 show($('#cOverOut'),o==null?null:verdict(po,pu,buf,o));show($('#cUnderOut'),u==null?null:verdict(pu,po,buf,u))}
if(body){[selD,selS].forEach(e=>e.addEventListener('change',()=>{renderProps();if(cur)openCalc(cur)}));q.addEventListener('input',renderProps);
 ['#cLine','#cOver','#cUnder'].forEach(id=>$(id).addEventListener('input',runCalc));renderProps()}
})();
"""


def pct(x, d=0):
    return "–" if x is None else f"{x * 100:.{d}f}%"


def f1(x, d=1):
    return "–" if x is None else f"{x:.{d}f}"


def implied(am):
    return 1 / am_dec(am) if am is not None else None


def price_bar(m, show_mark=True):
    """Value / lean / avoid zones in implied probability, with the book's price marked."""
    if m.get("fair") is None or m.get("bet_at") is None:
        return ""
    qb, qf = implied(m["bet_at"]), implied(m["fair"])
    lo, hi = max(0.01, qb - 0.09), min(0.99, qf + 0.07)
    if m.get("book") is not None:
        qk = implied(m["book"])
        lo, hi = min(lo, qk - 0.02), max(hi, qk + 0.02)
    span = hi - lo

    def pos(q):
        return max(0.0, min(100.0, (q - lo) / span * 100))
    zv, zl = pos(qb), pos(qf) - pos(qb)
    mark = ""
    cls = "pbar"
    if show_mark and m.get("book") is not None:
        x = pos(implied(m["book"]))
        mark = (f'<div class="mark" style="left:{x:.1f}%"></div>'
                f'<div class="mlab" style="left:{min(92, max(8, x)):.1f}%">Book {fmt_am(m["book"])}</div>')
        cls += " withmark"
    ticks = (f'<span style="left:{min(88, max(10, pos(qb))):.1f}%">Bet at {fmt_am(m["bet_at"])}</span>'
             f'<span style="left:{min(90, max(30, pos(qf) + 6)):.1f}%">Fair {fmt_am(m["fair"])}</span>')
    aria = f'Value at {fmt_am(m["bet_at"])} or better, lean to {fmt_am(m["fair"])}, avoid worse'
    return (f'<div class="{cls}" role="img" aria-label="{esc(aria)}"><div class="track">'
            f'<div class="z zv" style="width:{zv:.1f}%"></div><div class="z zl" style="width:{zl:.1f}%"></div>'
            f'<div class="z za" style="flex:1"></div></div>{mark}<div class="ticks">{ticks}</div></div>')


def vtag(v):
    return {"value": '<span class="tag value">Value</span>', "lean": '<span class="tag lean">Lean</span>',
            "avoid": '<span class="tag avoid">Avoid</span>'}.get(v, '<span class="tag muted">No price</span>')


def day_label(d, today):
    dd = ddate(d)
    if dd == today:
        return "Today"
    if dd == today + dt.timedelta(days=1):
        return "Tomorrow"
    return dd.strftime("%a %b ") + str(dd.day)


def team_name(c, tid, short=False):
    x = c.team_stats.get(tid) or {}
    return x.get("short" if short else "name") or x.get("abbr") or str(tid)


def market_rows(ms, show_line_input=False):
    out = []
    for m in ms:
        attrs = f'data-p="{m["p"]:.5f}" data-pl="{m["pl"]:.5f}" data-buf="{m["buf"]}"'
        lncell = ""
        if m.get("mu") is not None:
            attrs += f' data-mu="{m["mu"]:.3f}" data-sd="{m["sd"]:.3f}" data-kind="{m["kind"]}" data-side="{m.get("side", "")}"'
            disp = m["line"] if m["kind"] == "total" else m["line"]
            lncell = f'<input class="ln" inputmode="decimal" aria-label="Line for {esc(m["label"])}" value="{disp:g}">'
            if m["est_line"]:
                lncell += ' <span class="dim" title="Estimated line: type your book\'s line">est.</span>'
        bk = fmt_am(m["book"]) if m["book"] is not None else ""
        mk = pct(m["mkt_p"]) if m.get("mkt_p") is not None else "–"
        out.append(
            f'<tr {attrs}><td class="l">{esc(m["label"])}</td><td class="l">{lncell}</td>'
            f'<td class="pc">{pct(m["p"])}</td><td class="dim">{mk}</td><td class="fa">{fmt_am(m["fair"])}</td>'
            f'<td class="ba">{fmt_am(m["bet_at"])}</td>'
            f'<td><input class="bk" inputmode="text" aria-label="Your price for {esc(m["label"])}" value="{bk}" placeholder="-110"></td>'
            f'<td class="l"><span class="out"></span></td></tr>')
    return "".join(out)


def market_table(ms):
    head = ('<tr><th class="l">Bet</th><th class="l">Line</th><th>Our %</th><th>Market %</th><th>Fair</th>'
            '<th>Bet at</th><th>Your price</th><th class="l">Verdict</th></tr>')
    return f'<div class="tbl-wrap"><table><thead>{head}</thead><tbody>{market_rows(ms)}</tbody></table></div>'


def rank_txt(r):
    return f"#{r} " if r else ""


def team_label(c, tid, abbr_only=False):
    T = c.team_stats.get(tid)
    if T:
        return f'{rank_txt(T["rank"])}{T["abbr"] if abbr_only else (T["short"] or T["name"])}'
    m = c.db.teams.get(tid, {})
    return m.get("abbr" if abbr_only else "short") or m.get("name") or str(tid)


def render_top(c, top, gaps, watch, pchecks, summ, analyses):
    t = summ["top"]
    rec = (f'<div class="record"><div><b>{t["w"]}-{t["l"]}{"-" + str(t["p"]) if t["p"] else ""}</b> top bets graded</div>'
           f'<div><b>{t["units"]:+.1f}u</b> profit at 1 unit each</div>'
           f'<div><b>{pct(t["roi"], 1) if t["roi"] is not None else "–"}</b> ROI</div></div>') if t["n"] else \
          '<div class="record"><div>No top bets graded yet. The record starts filling in after the first games finish.</div></div>'
    parts = ['<h2>Top bets</h2>',
             '<p class="lede">The best spots across every Division I game with a posted price, alternating between bets '
             'the model gives a high chance to win and bets with the biggest edge. Books post most college lines the day '
             'before, so later days fill in as the week goes. On each price bar, green is a deal, amber is thin and red '
             'is a pass; the black mark is the book\'s current price.</p>', rec]
    if top:
        by_day = {}
        for x in top:
            by_day.setdefault(x["ga"]["g"]["date"], []).append(x)
        i = 0
        for d in sorted(by_day):
            parts.append(f'<h3>{esc(day_label(d, c.today))}</h3><ol class="bets">')
            for x in by_day[d]:
                i += 1
                ga, m = x["ga"], x["m"]
                g = ga["g"]
                tagcls = "value" if "value" in x["tag"].lower() else ""
                parts.append(
                    f'<li class="panel"><div class="rank">{i}</div><div>'
                    f'<div class="bet-h"><span class="pick">{esc(m["label"])}</span><span class="price num">{fmt_am(m["book"])}</span>'
                    f'<span class="tag {tagcls}">{esc(x["tag"])}</span></div>'
                    f'<div class="bet-sub">{esc(team_label(c, g["away"]))} at {esc(team_label(c, g["home"]))}'
                    f'{" (neutral)" if g["neutral"] else ""}, {esc(fmt_time(g["utc"]))}'
                    f'{(" on " + esc(g["tv"])) if g.get("tv") else ""}</div>'
                    f'{price_bar(m)}'
                    f'<div class="facts"><div><span>Win chance</span> <b>{pct(m["p"])}</b></div>'
                    f'<div><span>Market</span> <b>{pct(m["mkt_p"])}</b></div>'
                    f'<div><span>Expected return</span> <b>{m["ev"] * 100:+.1f}%</b></div>'
                    f'<div><span>Bet down to</span> <b>{fmt_am(m["bet_at"])}</b></div></div>'
                    f'<p class="why">{esc(top_reason(c, ga, m))}</p></div></li>')
            parts.append('</ol>')
        if len(top) < CONFIG["top_bets_min"]:
            parts.append(f'<p class="note">Only {len(top)} bets clear the bar right now. The list stays short rather than '
                         f'filling up with weak picks.</p>')
    else:
        n_priced = sum(1 for ga in analyses if ga["sp_line"] is not None or ga["tot_line"] is not None)
        msg = ("No sportsbook prices were found this run, so there is nothing to compare against yet. College lines "
               "usually go up the day before each game; run the script again then. Until then, use the watch list "
               "below and the model lines on each game.") if not n_priced else \
              "No bet clears the bar at current prices. That happens: passing is a position."
        parts.append(f'<div class="panel empty">{msg}</div>')
    if watch:
        parts.append(f'<details class="watch"><summary><h3 style="display:inline-block">Lines to watch</h3> '
                     f'<span class="dim">{len(watch)} Division I games without a line yet</span></summary><p class="note">When the '
                     'book opens these games, bet a side only at the number shown or better. The model is blended with the '
                     'market, so it takes a big gap to make a bet worth it.</p>')
        rows = []
        for w in watch:
            ga = w["ga"]
            g = ga["g"]
            rows.append(f'<tr><td class="l">{esc(day_label(g["date"], c.today))}</td>'
                        f'<td class="l">{esc(team_label(c, g["away"], True))} @ {esc(team_label(c, g["home"], True))}</td>'
                        f'<td>{esc(fsp(g["habbr"], -ga["mm"]))}</td><td>{ga["mt"]:.1f}</td><td>{pct(ga["win_h"])}</td>'
                        f'<td>{esc(fsp(g["habbr"], -w["th_h"]))}</td><td>{esc(fsp(g["aabbr"], w["th_a"]))}</td></tr>')
        parts.append('<div class="panel tbl-wrap"><table><thead><tr><th class="l">Day</th><th class="l">Game</th>'
                     '<th>Model spread</th><th>Model total</th><th>Home win</th><th>Bet home at</th><th>Bet away at</th>'
                     f'</tr></thead><tbody>{"".join(rows)}</tbody></table></div></details>')
    if pchecks:
        parts.append('<h3>Props to price-check</h3><p class="note">No sportsbook price was fetched for these, so they '
                     'can\'t be top bets. They are the biggest gaps between the projection and each player\'s recent '
                     'average. Take the over at or below the first number, the under at or above the second, at around '
                     '-110. The Props tab prices any line exactly.</p>')
        rows = []
        for x in pchecks:
            ga, pr, k, st = x["ga"], x["pr"], x["k"], x["st"]
            g = ga["g"]
            side = "Over" if x["z"] > 0 else "Under"
            th = st["over_upto"] if x["z"] > 0 else st["under_from"]
            rows.append(f'<tr><td class="l">{esc(pr["name"])}</td><td class="l">{esc(team_label(c, pr["tid"], True))} vs '
                        f'{esc(team_label(c, pr["opp"], True))}, {esc(day_label(g["date"], c.today))}</td>'
                        f'<td class="l">{STAT_NAMES[k]}</td><td><b>{st["mu"]:.1f}</b></td><td>{f1(x["ref"])}</td>'
                        f'<td>{f1(pr["min"])}</td><td class="l"><b>{side}</b> {"≤" if side == "Over" else "≥"} {th if th is not None else "–"}</td></tr>')
        parts.append('<div class="panel tbl-wrap"><table><thead><tr><th class="l">Player</th><th class="l">Game</th>'
                     '<th class="l">Stat</th><th>Projection</th><th title="This season blended with last season until about 6 games in">Recent avg</th><th>Minutes</th><th class="l">Look for</th>'
                     f'</tr></thead><tbody>{"".join(rows)}</tbody></table></div>')
    if gaps:
        parts.append('<h3>Big model vs market gaps</h3><p class="note">The model and the books disagree by a lot here. In '
                     'the 2025-26 test, spread disagreements of 6+ points went against the model, which usually means '
                     'news it can\'t see (a suspension, a player sitting, a transfer). These are kept off the list.</p><ul class="guide">')
        for ga, m in gaps[:10]:
            parts.append(f'<li>{esc(m["label"])} ({esc(ga["g"]["aabbr"])} @ {esc(ga["g"]["habbr"])}): model {pct(m["model_p"])} vs market {pct(m["mkt_p"])}</li>')
        parts.append('</ul>')
    return "".join(parts)


def top_reason(c, ga, m):
    g = ga["g"]
    H, A = g["habbr"], g["aabbr"]
    bits = []
    grp = m["group"]
    if grp in ("Spread", "Moneyline"):
        bits.append(f"Model alone has {fsp(H, -ga['mm'])}" + (f" vs the market's {fsp(H, ga['sp_line'])}" if ga["sp_line"] is not None else ""))
    elif grp == "Total":
        bits.append(f"Model total {ga['mt']:.1f} vs {ga['tot_line']:g}")
    elif grp == "Player prop":
        ref = f", {m['ref_lbl']} {m['ref']:.1f}" if m.get("ref") is not None else ""
        hits = m.get("hits") or (0, 0)
        side = "over" if m["key"].endswith("_O") else "under"
        bits.append(f"Projects {m['proj']:.1f} {m['stat']} in {m['minutes']:.0f} minutes vs a line of {m['line']:g}{ref}")
        if hits[1]:
            bits.append(f"Went {side} this line in {hits[0]} of his last {hits[1]}")
    for tid, ab in ((g["home"], H), (g["away"], A)):
        inj = ga["inj"].get(tid) or {}
        tot = inj.get("total", 0.0)
        if tot >= 1.0:
            names = [r["name"] for r in inj.get("rows", []) if r["pp"] <= 0.55][:2]
            bits.append(f"{ab} may be without {', '.join(names) or 'rotation players'} (about {tot:.1f} pts)")
    for tid, ab in ((g["home"], H), (g["away"], A)):
        x = c.team_stats.get(tid)
        if x and abs(x["shift"]) >= 3 and (c.gp.get(tid, 0) < 6):
            bits.append(f"{ab} roster {'gained' if x['shift'] > 0 else 'lost'} about {abs(x['shift']):.1f} pts of value since last season")
    return ". ".join(bits) + "."


def ordinal(n):
    if n is None:
        return "–"
    n = int(n)
    suf = "th" if 10 <= n % 100 <= 20 else {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")
    return f"{n}{suf}"


STAT_ROWS = [
    ("adj_net", "Model rating (pts/100 vs avg D1)", "+1"),
    ("adj_o", "Model offence (pts/100)", "1"),
    ("adj_d", "Model defence (pts/100 allowed)", "1"),
    ("adj_pace", "Model tempo (poss/40)", "1"),
    ("net", "Net rating", "+1"),
    ("ortg", "Offensive rating", "1"),
    ("drtg", "Defensive rating", "1"),
    ("pace", "Tempo", "1"),
    ("ppg", "Points per game", "1"),
    ("oppg", "Points allowed", "1"),
    ("efg", "Effective FG%", "%"),
    ("oefg", "Opponent effective FG%", "%"),
    ("3par", "3-point attempt rate", "%"),
    ("3pct", "3-point %", "%"),
    ("o3pct", "Opponent 3-point %", "%"),
    ("tovp", "Turnovers per 100", "%"),
    ("otovp", "Forced turnovers per 100", "%"),
    ("orbp", "Offensive rebound %", "%"),
    ("drbp", "Defensive rebound %", "%"),
    ("ftr", "Free throw rate", "%"),
    ("oftr", "Opponent free throw rate", "%"),
]


def _r(x, d=1):
    return None if x is None else round(float(x), d)


def teams_json(c, tids):
    """Compact team data the game cards draw from (each team stored once)."""
    out = {}
    for t in tids:
        x = c.team_stats.get(t)
        if not x:
            m = c.db.teams.get(t, {})
            out[t] = {"ab": m.get("abbr") or str(t), "nm": m.get("name") or str(t), "d1": 0}
            continue
        st = []
        for k, lab, fmt in STAT_ROWS:
            v = x.get(k)
            if v is not None and fmt == "%":
                v = v * 100
            st.append([_r(v), x.get("rk_" + k)])
        res = [[r["date"], team_label(c, r["opp"], True), 1 if r["neutral"] else (0 if r["home"] else 2),
                r["pf"], r["pa"], r["ats"] or "", r["ou"] or ""] for r in x["res"][-5:]]
        out[t] = {"ab": x["abbr"], "nm": x["name"], "d1": 1, "rk": x["rank"], "cf": x["conf"],
                  "wl": f'{x["w"]}-{x["l"]}', "cwl": f'{x["cw"]}-{x["cl"]}', "cr": x.get("conf_rank"),
                  "hm": f'{x["hw"]}-{x["hl"]}', "rd": f'{x["aw"]}-{x["al"]}', "nu": f'{x["nw"]}-{x["nl"]}',
                  "ats": "-".join(str(v) for v in (x["ats"][:2] + ([x["ats"][2]] if x["ats"][2] else []))),
                  "ou": "-".join(str(v) for v in (x["ou"][:2] + ([x["ou"][2]] if x["ou"][2] else []))),
                  "l10": x["l10"], "sk": x["streak"], "net": _r(x["adj_net"]), "pw": x["power"],
                  "sh": _r(x["shift"]), "gp": x["g"], "st": st, "last": res}
    return out


def game_json(c, ga):
    g = ga["g"]
    mk = []
    for m in ga["markets"]:
        mk.append([m["label"], m["line"], round(m["p"], 4), round(m["pl"], 4), None if m["mkt_p"] is None else round(m["mkt_p"], 3),
                   m["fair"], m["bet_at"], m["book"], m["buf"], None if m.get("mu") is None else round(m["mu"], 2),
                   None if m.get("sd") is None else round(m["sd"], 2), m.get("kind", ""), m.get("side", ""),
                   1 if m["est_line"] else 0, m["group"]])
    inj = {}
    for tid in (g["away"], g["home"]):
        rows = (ga["inj"].get(tid) or {}).get("rows", [])
        inj[tid] = [[r["name"], r["status"], r.get("detail") or "", _r(r.get("mpg")), _r(r.get("ppg")), _r(r.get("imp")),
                     round(r["pp"], 2)] for r in rows[:8]]
    pl = {}
    for tid in (g["away"], g["home"]):
        rows = []
        for p in sorted((p for p in ga["props"] if p["tid"] == tid), key=lambda p: -p["min"])[:9]:
            s_ = p["stats"]
            rows.append([p["short"], _r(p["min"], 0), _r(p["m_l5"], 0), _r(p["m_season"], 0)]
                        + [[_r(s_[k]["mu"]), s_[k]["over_upto"], s_[k]["under_from"]] for k in ("pts", "reb", "ast", "fg3m", "pra")]
                        + [round(p["pp"], 2)])
        pl[tid] = rows
    h2h = [[gm["date"], team_label(c, gm["away"], True), gm["as"], team_label(c, gm["home"], True), gm["hs"]] for gm in ga["h2h"][:4]]
    return {"a": g["away"], "h": g["home"], "gd": [[k, t] for k, t in guide_for(c, ga)], "mk": mk, "inj": inj, "pl": pl,
            "h2h": h2h, "rest": list(ga["rest"]), "adj": [_r(ga["adj"][1], 2), _r(ga["adj"][0], 2)],
            "venue": g.get("venue") or "", "note": g.get("note") or ""}


def game_row(c, ga):
    """One line per game in the list; the details are drawn from GAMES/TEAMS data when it's opened."""
    g = ga["g"]
    T = c.team_stats
    priced = [m for m in ga["markets"] if m["verdict"] == "value"]
    best = max(priced, key=lambda m: m["ev_c"]) if priced else None
    if g["state"] != "pre":
        chip = f'<span class="chip none">{esc(g["detail"] or "Final")}</span>'
    elif best:
        chip = f'<span class="chip">{esc(best["label"])} {fmt_am(best["book"])}</span>'
    elif ga["sp_line"] is None:
        chip = '<span class="chip none">No line yet</span>'
    else:
        chip = '<span class="chip none">No edge</span>'
    bh, ba = (ga["bt"] + ga["bm"]) / 2, (ga["bt"] - ga["bm"]) / 2

    def tm(tid, proj, score, rk):
        x = T.get(tid)
        m = c.db.teams.get(tid, {})
        ab = (x or {}).get("abbr") or m.get("abbr") or "?"
        nm = (x or {}).get("short") or m.get("short") or m.get("name") or ""
        rec = f'{x["w"]}-{x["l"]}, {x["conf"]}' if x else "non-D1"
        rk = rk or (x or {}).get("rank")
        right = f'{int(score)}' if score is not None else f'{proj:.0f}'
        return (f'<div class="tm">{f"<span class=rk>{rk}</span>" if rk else "<span class=rk></span>"}'
                f'<span class="ab">{esc(ab)}</span><span class="nm">{esc(nm)}</span>'
                f'<span class="rec">{esc(rec)}</span><span class="proj num">{right}</span></div>')
    mkt = []
    if ga["sp_line"] is not None:
        mkt.append(f'Line <b>{esc(fsp(g["habbr"], ga["sp_line"]))}</b>')
    if ga["tot_line"] is not None:
        mkt.append(f'total <b>{ga["tot_line"]:g}</b>')
    mline = ", ".join(mkt) if mkt else "No line yet"
    where = " · neutral" if g["neutral"] else ""
    ranked = 1 if (g.get("hrank") or g.get("arank") or (T.get(g["home"]) or {}).get("rank") or (T.get(g["away"]) or {}).get("rank")) else 0
    confs = " ".join(sorted({str((T.get(t) or {}).get("conf_id", "")) for t in (g["home"], g["away"])}))
    search = " ".join(filter(None, [(T.get(t) or {}).get("name") or c.db.teams.get(t, {}).get("name", "") for t in (g["home"], g["away"])]
                             + [g["habbr"] or "", g["aabbr"] or ""])).lower()
    attrs = (f'data-gid="{esc(g["gid"])}" data-day="{g["date"]}" data-rk="{ranked}" data-line="{1 if ga["sp_line"] is not None else 0}" '
             f'data-conf="{esc(confs)}" data-q="{esc(search)}" data-val="{1 if best else 0}"')
    return (f'<details class="game panel" {attrs}><summary><div class="match">{tm(g["away"], ba, g.get("as") if g["state"] != "pre" else None, g.get("arank"))}'
            f'{tm(g["home"], bh, g.get("hs") if g["state"] != "pre" else None, g.get("hrank"))}</div>'
            f'<div class="sline"><span>{esc(fmt_time(g["utc"]))}{(" on " + esc(g["tv"])) if g.get("tv") else ""}{where}</span>'
            f'<span>{mline}</span><span>Model <b>{esc(fsp(g["habbr"], -ga["mm"]))}</b>, total <b>{ga["mt"]:.1f}</b>, '
            f'{esc(g["habbr"])} wins <b>{pct(ga["win_h"])}</b></span></div>'
            f'<div class="best">{chip}</div></summary><div class="gbody"></div></details>')


def render_games(c, analyses, days):
    parts = ['<h2>Games</h2><p class="lede">Every Division I game this week. Pick a day, search for a team or filter, then '
             'open a game for how to bet it, the full betting board, who\'s missing, projected minutes and player numbers, '
             'form and stat ranks.</p>']
    counts = {}
    for ga in analyses:
        counts[ga["g"]["date"]] = counts.get(ga["g"]["date"], 0) + 1
    first = next((d for d in days if counts.get(d)), days[0])
    btns = []
    for d in days:
        n = counts.get(d, 0)
        btns.append(f'<button aria-pressed="{"true" if d == first else "false"}" data-day="{d}"><b>{esc(day_label(d, c.today))}</b>'
                    f'<span>{n} game{"s" if n != 1 else ""}</span></button>')
    btns.append(f'<button aria-pressed="false" data-day="all"><b>All week</b><span>{len(analyses)} games</span></button>')
    parts.append('<div class="days" role="group" aria-label="Filter by day">' + "".join(btns) + '</div>')
    copts = "".join(f'<option value="{cid}">{esc(CONF_NAMES[cid][0])}</option>'
                    for cid in sorted(CONF_NAMES, key=lambda k: CONF_NAMES[k][0]) if cid in set(c.db.conf.values()))
    parts.append('<div class="controls"><label>Search <input id="gSearch" type="search" placeholder="Team, whole week"></label>'
                 '<label>Show <select id="gShow"><option value="all">All games</option><option value="line">Games with a line</option>'
                 '<option value="val">Games with a value bet</option><option value="rk">Ranked teams</option></select></label>'
                 f'<label>Conference <select id="gConf"><option value="">Any</option>{copts}</select></label>'
                 '<span class="dim" id="gCount" aria-live="polite"></span></div>')
    for d in days:
        gs = [ga for ga in analyses if ga["g"]["date"] == d]
        parts.append(f'<div class="daygroup" data-day="{d}"{"" if d == first else " hidden"}><h3>{esc(ddate(d).strftime("%A, %B ") + str(ddate(d).day))}</h3>')
        if not gs:
            parts.append('<p class="note">No Division I games.</p>')
        for ga in sorted(gs, key=lambda x: (x["g"]["utc"] or dt.datetime.max, x["g"]["gid"])):
            parts.append(game_row(c, ga))
        parts.append('</div>')
    parts.append('<p class="note" id="gNone" hidden>No games match. Clear the search or pick another day.</p>')
    return "".join(parts)


def render_props_tab(c, analyses, days):
    rows = []
    keep = ("pts", "reb", "ast", "fg3m", "pra")
    for ga in analyses:
        g = ga["g"]
        if ga["d1"] != (True, True):
            continue
        for p in ga["props"]:
            if p["min"] < 18 and not any(p["stats"][k].get("book") for k in keep):
                continue
            st = {}
            for k in keep:
                x = p["stats"][k]
                bk = x.get("book") or {}
                st[k] = [round(x["mu"], 2), round(x["var"], 2), x["fair"], x["over_upto"], x["under_from"],
                         _r(x["l10_avg"]), x["hit_fair"][0], x["hit_fair"][1], bk.get("line"), bk.get("over"),
                         bk.get("under"), _r(x["avg_cur"])]
            rows.append({"n": p["name"], "t": team_label(c, p["tid"], True), "o": team_label(c, p["opp"], True),
                         "h": p["tid"] == g["home"], "d": g["date"], "dl": day_label(g["date"], c.today),
                         "min": round(p["min"], 1), "l5": _r(p["m_l5"]), "pp": round(p["pp"], 2),
                         "status": "Missed recent games" if p["pp"] < 1 else "", "st": st})
    opts = '<option value="all">All week</option>' + "".join(
        f'<option value="{d}"{" selected" if i == 0 else ""}>{esc(day_label(d, c.today))}</option>' for i, d in enumerate(days))
    sopts = "".join(f'<option value="{k}">{STAT_NAMES[k]}</option>' for k in keep)
    html_ = f"""<h2>Player props</h2>
<p class="lede">Projections for players expected to play 18+ minutes in Division I games this week. Fair is the line the
model sees as a coin flip. Over ≤ and Under ≥ are where a -110 bet has an edge after the safety margin. Click a player to
price any line and odds.</p>
<div class="controls"><label>Day <select id="pDay">{opts}</select></label><label>Stat <select id="pStat">{sopts}</select></label>
<label>Search <input id="pSearch" type="search" placeholder="Player or team"></label></div>
<div class="panel calc" id="pCalc" aria-live="polite"><h3 id="cName" style="margin-top:0"></h3><p class="note" id="cInfo"></p>
<div class="controls"><label>Line <input id="cLine" inputmode="decimal" size="5"></label>
<label>Over price <input id="cOver" size="6"></label> <span class="out" id="cOverOut"></span>
<label>Under price <input id="cUnder" size="6"></label> <span class="out" id="cUnderOut"></span></div><p id="cProb" class="mini"></p></div>
<div class="panel tbl-wrap"><table><thead><tr><th class="l">Player</th><th class="l">Game</th><th class="l">Day</th><th>Min</th><th>L5 min</th>
<th>Proj.</th><th>Fair</th><th>Over ≤</th><th>Under ≥</th><th>L10 avg</th><th>L10 over fair</th><th>Season</th><th>Book</th></tr></thead>
<tbody id="pBody"></tbody></table></div><p class="note" id="pMore"></p>"""
    data = (f"<script>window.PROPS={json.dumps(rows, separators=(',', ':'))};"
            f"window.STATNAMES={json.dumps({k: STAT_NAMES[k] for k in keep})};window.PROPBUF={CONFIG['buffer_props']};</script>")
    return html_, data


def render_injuries_tab(c, analyses):
    parts = ['<h2>Who\'s missing</h2><p class="lede">College programs don\'t publish injury reports, so this lists rotation '
             'players (15+ minutes a game) who missed their team\'s most recent game or games. The model treats a player '
             'who missed the last game as 55% to play, two straight as 25%, three or more as 12%. Value is what he is worth '
             'per game over a replacement player, in points of margin. Check team news before betting.</p>']
    rows = []
    seen = set()
    for ga in analyses:
        for tid in (ga["g"]["away"], ga["g"]["home"]):
            if tid in seen:
                continue
            seen.add(tid)
            for r in (ga["inj"].get(tid) or {}).get("rows", []):
                rows.append((tid, ga, r))
    rows.sort(key=lambda x: -(x[2].get("imp") or 0))
    body = "".join(
        f'<tr><td class="l">{esc(team_label(c, tid))}</td><td class="l">{esc(r["name"])}</td>'
        f'<td class="l"><span class="tag {"avoid" if r["pp"] <= 0.25 else "lean"}">{esc(r["status"])}</span></td>'
        f'<td data-s="{r.get("mpg") or 0}">{f1(r.get("mpg"))}</td><td data-s="{r.get("ppg") or 0}">{f1(r.get("ppg"))}</td>'
        f'<td data-s="{(r.get("imp") or 0):.2f}">{(r.get("imp") or 0):.1f}</td><td>{pct(r["pp"])}</td>'
        f'<td class="l">{esc(day_label(ga["g"]["date"], c.today))}: {esc(ga["g"]["aabbr"])} @ {esc(ga["g"]["habbr"])}</td></tr>'
        for tid, ga, r in rows)
    parts.append('<div class="panel tbl-wrap"><table class="sortable"><thead><tr><th class="l">Team</th><th class="l">Player</th>'
                 '<th class="l">Status</th><th>Min</th><th>Pts</th><th>Value</th><th>Plays</th><th class="l">Next game</th>'
                 f'</tr></thead><tbody>{body or "<tr><td class=l colspan=8>No rotation players have missed recent games.</td></tr>"}</tbody></table></div>')
    return "".join(parts)


def render_standings(c):
    T = c.team_stats
    parts = ['<h2>Rankings and standings</h2><p class="lede">The model\'s rating is points per 100 possessions better than an '
             'average Division I team on a neutral floor, adjusted for opponents. Early in the season it leans on last season '
             'and roster moves (the Roster Δ column). Click a column to sort.</p>']
    top = sorted(T.values(), key=lambda x: -x["adj_net"])[:75]
    rows = "".join(
        f'<tr><td data-s="{x["power"]}">{x["power"]}</td><td class="l">{esc(rank_txt(x["rank"]))}{esc(x["name"])}</td>'
        f'<td class="l">{esc(x["conf"])}</td><td data-s="{x["pct"]:.4f}">{x["w"]}-{x["l"]}</td>'
        f'<td data-s="{x["adj_net"]:.3f}"><b>{x["adj_net"]:+.1f}</b></td><td data-s="{x["adj_o"]:.2f}">{x["adj_o"]:.1f}</td>'
        f'<td data-s="{x["adj_d"]:.2f}">{x["adj_d"]:.1f}</td><td data-s="{x["adj_pace"]:.2f}">{x["adj_pace"]:.1f}</td>'
        f'<td>{x["ats"][0]}-{x["ats"][1]}</td><td data-s="{x["shift"]:.2f}">{x["shift"]:+.1f}</td></tr>' for x in top)
    head = ('<tr><th>#</th><th class="l">Team</th><th class="l">Conf</th><th>W-L</th><th>Rating</th><th>Adj. off</th>'
            '<th>Adj. def</th><th>Tempo</th><th>ATS</th><th title="Margin points per game gained or lost through roster moves since last season">Roster Δ</th></tr>')
    parts.append(f'<h3>Model top 75</h3><div class="panel tbl-wrap"><table class="sortable"><thead>{head}</thead><tbody>{rows}</tbody></table></div>')
    parts.append('<h3>Conference standings</h3>')
    confs = sorted({x["conf_id"] for x in T.values()}, key=lambda cid: -np.mean([x["adj_net"] for x in T.values() if x["conf_id"] == cid]))
    for cid in confs:
        xs = sorted([x for x in T.values() if x["conf_id"] == cid], key=lambda x: x.get("conf_rank") or 99)
        avg = np.mean([x["adj_net"] for x in xs])
        rows = "".join(
            f'<tr><td>{x["conf_rank"]}</td><td class="l">{esc(rank_txt(x["rank"]))}{esc(x["name"])}</td><td>{x["cw"]}-{x["cl"]}</td>'
            f'<td>{x["w"]}-{x["l"]}</td><td>{x["hw"]}-{x["hl"]}</td><td>{x["aw"]}-{x["al"]}</td><td>{x["nw"]}-{x["nl"]}</td>'
            f'<td>{x["streak"] or "–"}</td><td data-s="{x["adj_net"]:.3f}"><b>{x["adj_net"]:+.1f}</b></td><td>{x["power"]}</td>'
            f'<td>{x["ats"][0]}-{x["ats"][1]}</td><td>{x["ou"][0]}-{x["ou"][1]}</td></tr>' for x in xs)
        parts.append(f'<details class="conf panel"><summary><b>{esc(CONF_NAMES.get(cid, ("?", "?"))[1])}</b> '
                     f'<span class="dim">{len(xs)} teams, average rating {avg:+.1f}</span></summary><div class="tbl-wrap">'
                     '<table class="sortable"><thead><tr><th>#</th><th class="l">Team</th><th>Conf</th><th>W-L</th><th>Home</th>'
                     '<th>Road</th><th>Neutral</th><th>Streak</th><th>Rating</th><th>Rank</th><th>ATS</th><th>O/U</th></tr></thead>'
                     f'<tbody>{rows}</tbody></table></div></details>')
    return "".join(parts)


def render_track(c, summ):
    parts = ['<h2>Track record</h2><p class="lede">Every run logs the pre-game probability for each market. After games '
             'finish they are graded here, so you can see which markets the model is actually good at before trusting it.</p>']
    t = summ["top"]
    parts.append(f'<h3>Top bets</h3><div class="record"><div><b>{t["w"]}-{t["l"]}{"-" + str(t["p"]) if t["p"] else ""}</b> record</div>'
                 f'<div><b>{t["units"]:+.2f}u</b> profit</div><div><b>{pct(t["roi"], 1) if t["roi"] is not None else "–"}</b> ROI</div></div>')
    items = [v for v in summ["top_items"] if v.get("result")]
    if items:
        rows = "".join(f'<tr><td class="l">{v["date"]}</td><td class="l">{esc(v["game"])}</td><td class="l">{esc(v["label"])}</td>'
                       f'<td>{fmt_am(v["book"])}</td><td>{pct(v["p"])}</td><td class="l">{esc(v.get("tag", ""))}</td>'
                       f'<td class="l"><span class="{"v" if v["result"] == "W" else "a" if v["result"] == "L" else "dim"}">{v["result"]}</span></td></tr>'
                       for v in items[:60])
        parts.append('<div class="panel tbl-wrap"><table><thead><tr><th class="l">Date</th><th class="l">Game</th><th class="l">Bet</th>'
                     f'<th>Price</th><th>Win %</th><th class="l">Type</th><th class="l">Result</th></tr></thead><tbody>{rows}</tbody></table></div>')
    else:
        parts.append('<p class="note">Nothing graded yet.</p>')
    rows = "".join(
        f'<tr><td class="l">{esc(g)}</td><td>{a["n"]}</td><td>{a["w"]}-{a["l"]}{"-" + str(a["p"]) if a["p"] else ""}</td>'
        f'<td>{pct(a["w"] / max(1, a["w"] + a["l"]), 1)}</td><td>{a["brier"]:.3f}</td>'
        f'<td>{(format(a["units"], "+.1f") + "u") if a["staked"] else "–"}</td></tr>'
        for g, a in summ["groups"] if a["n"])
    parts.append('<h3>Every market, side the model favoured</h3>')
    parts.append('<div class="panel tbl-wrap"><table><thead><tr><th class="l">Market</th><th>Graded</th><th>W-L</th><th>Hit rate</th>'
                 '<th title="Lower is better; 0.25 is a coin flip">Brier</th><th>Profit where priced</th></tr></thead>'
                 f'<tbody>{rows or "<tr><td class=l colspan=6>Nothing graded yet.</td></tr>"}</tbody></table></div>')
    parts.append('<p class="note">Hit rate here counts every game\'s favoured side, edge or not, so expect it to sit a little '
                 'above 50% for spreads and totals. The top bets record is the one that matters for betting.</p>')
    return "".join(parts)


def render_how(c):
    C = CONFIG
    return f"""<h2>How it works</h2><div class="how">
<p><b>Data.</b> Box scores for this season and last come from ESPN via the sportsdataverse data releases on GitHub,
topped up with ESPN game summaries for anything newer. The schedule, sportsbook lines (ESPN's odds feed, usually
DraftKings), AP rankings and rosters come from ESPN's public API. Every Division I game is modelled; non-Division I
opponents share one rating.</p>
<p><b>Team ratings.</b> Each team gets an offensive, defensive and tempo rating per 100 possessions, adjusted for
opponent and home court (neutral sites count as neutral), from a weighted regression where a game {C['hl_days']} days
ago counts half as much as last night. The preseason rating starts from last season: the team's level relative to its
conference keeps {round(C['prior_regress'] * 100)}%, the conference's level is kept in full, and roster moves are added
on top. Returning players, transfers in and players lost are valued by their game score per 40 minutes; freshmen and
newcomers without Division I history count as a little above replacement. That preseason rating is worth about
{C['prior_games']} games, so by mid-December this season's results dominate.</p>
<p><b>Who's missing.</b> College programs don't publish injury reports. A rotation player (15+ minutes) who missed the
team's last game is treated as 55% to play, two straight as 25%, three or more as 12%. In the 2025-26 test this helped
only a little, so the adjustment is kept light. Check team news before betting.</p>
<p><b>Game estimate.</b> Tempo times efficiency gives each team's points. For betting, the model is blended with the
market when a line is posted: {round(C['w_model_margin'] * 100)}% model on the spread and moneyline,
{round(C['w_model_total'] * 100)}% on totals. Results land within about {C['sd_margin']:g} points of the spread estimate
and {C['sd_total']:g} of the total estimate (one standard deviation), which sets every probability. First-half lines use
the same estimate scaled to the half.</p>
<p><b>How good is it?</b> Re-run day by day through 2025-26 with no hindsight and checked against 1,454 real DraftKings
closing lines, the model alone missed the final margin by 11.3 points (root mean square) against 11.0 for the closing
spread, and blends with some model weight beat the line alone. The pick rule used here (35% model on sides, a 2-point
safety margin, nothing where the model is 6+ points off the spread) went 127-102 on spreads (55.5%, +7.3% per bet) and
returned +4.2% on moneylines at closing prices. On totals the line was better than the model (17.0 vs 17.2 points), so
totals need a much bigger edge and rarely make the list. Those settings were chosen on the same games, so expect real
results to be thinner. Disagreements of 6+ points went 19-25 for the model, which usually means the market knew
something: those are listed as warnings, not bets.</p>
<p><b>Players.</b> Minutes come from recent games for the current team (coach's-decision DNPs count as zero), blended
with last season, then spread to 200 per team, capped at {C['max_minutes']:.0f}. Per-minute rates weight recent games
most and are scaled so the team's players add up to its projected points, with tempo and the opponent's rebounds and
assists allowed. Each stat's spread comes from the player's own game log, widened for uncertainty.</p>
<p><b>Odds.</b> Fair is the break-even price for our probability. Bet at subtracts a safety margin
({round(C['buffer_main'] * 100, 1)} points for sides, {round(C['buffer_total'] * 100, 1)} for game totals, {round(C['buffer_derived'] * 100, 1)} for team totals and
halves, {round(C['buffer_props'] * 100, 1)} for props). At Bet at or better is value, between Bet at and Fair is a lean,
worse than Fair is a pass.</p>
<p><b>Top bets.</b> Only markets with a real sportsbook price qualify. A pick is either high probability (our
{round(C['high_prob_min'] * 100)}%+) or value, and every pick must beat the Bet-at price (the rule tested above). The
list alternates between the two, takes at most {C['max_per_game']} per game and never both sides of one market, and
skips sides where the model alone is {C['max_gap_pts']:g}+ points off the spread or totals {C['max_gap_pts_total']:g}+ off.</p>
<p><b>Limits.</b> Suspensions, illnesses and players sitting aren't known until they miss a game. Lines move a lot on
small college games; get the best number you can. I'm not a financial advisor; bet only what you can afford to lose.</p></div>"""


def render_page(c, analyses, top, gaps, watch, pchecks, summ, days, alerts, run_info):
    props_html, props_data = render_props_tab(c, analyses, days)
    wk = f'{ddate(days[0]).strftime("%b ")}{ddate(days[0]).day} to {ddate(days[-1]).strftime("%b ")}{ddate(days[-1]).day}'
    al = "".join(f'<div class="alert">{esc(a)}</div>' for a in alerts)
    tids = sorted({t for ga in analyses for t in (ga["g"]["home"], ga["g"]["away"])})
    data = ("<script>window.TEAMS=" + json.dumps(teams_json(c, tids), separators=(",", ":")) +
            ";window.GAMES=" + json.dumps({ga["g"]["gid"]: game_json(c, ga) for ga in analyses}, separators=(",", ":")) +
            ";window.STATROWS=" + json.dumps([[lab, fmt] for k, lab, fmt in STAT_ROWS]) + ";</script>")
    data = data.replace("</", "<\\/").replace("<\\/script>", "</script>")
    return f"""<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>CBB Edge</title><meta name="description" content="College basketball betting board: top bets, every game by day, props and rankings">
<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Barlow+Condensed:wght@600;700&family=Barlow:wght@400;500;600&display=swap" rel="stylesheet">
<style>{CSS}</style></head><body>
<header class="top"><div class="wrap"><div class="brand"><h1>CBB Edge</h1>
<span class="meta">Week of {esc(wk)}</span><span class="meta">Updated {esc(run_info['updated'])}</span>
<button class="themebtn" id="themebtn" type="button">Light / dark</button></div>
<div class="alerts">{al}</div></div></header>
<nav class="tabs" aria-label="Sections"><div class="wrap" role="tablist">
<button role="tab" data-tab="top" aria-selected="true">Top bets</button><button role="tab" data-tab="games" aria-selected="false">Games</button>
<button role="tab" data-tab="props" aria-selected="false">Props</button><button role="tab" data-tab="inj" aria-selected="false">Who's missing</button>
<button role="tab" data-tab="stand" aria-selected="false">Rankings</button><button role="tab" data-tab="track" aria-selected="false">Track record</button>
<button role="tab" data-tab="how" aria-selected="false">How it works</button></div></nav>
<main class="wrap">
<section class="tab on" id="top">{render_top(c, top, gaps, watch, pchecks, summ, analyses)}</section>
<section class="tab" id="games">{render_games(c, analyses, days)}</section>
<section class="tab" id="props">{props_html}</section>
<section class="tab" id="inj">{render_injuries_tab(c, analyses)}</section>
<section class="tab" id="stand">{render_standings(c)}</section>
<section class="tab" id="track">{render_track(c, summ)}</section>
<section class="tab" id="how">{render_how(c)}</section>
</main>{props_data}{data}<script>{JS}</script></body></html>"""


# --------------------------------------------------------------------------
# Publishing to GitHub Pages
# --------------------------------------------------------------------------
def _git(args, cwd, check=True):
    r = subprocess.run(["git"] + args, cwd=cwd, capture_output=True, text=True)
    if check and r.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {(r.stderr or r.stdout).strip()}")
    return r


def publish(html_path, date_str):
    url, branch = CONFIG["repo_url"], CONFIG["branch"]
    if not url:
        return
    if not shutil.which("git"):
        log("  ! git is not installed, so the page was not published (see README)")
        return
    site = os.path.join(HERE, CONFIG["site_dir"])
    try:
        if not os.path.isdir(os.path.join(site, ".git")):
            if os.path.exists(site) and os.listdir(site):
                raise RuntimeError(f"{site} exists but is not a git checkout; move it aside and run again")
            log(f"  Cloning {url} ...")
            _git(["clone", url, site], HERE)
        remote_has = _git(["ls-remote", "--heads", "origin", branch], site, check=False).stdout.strip() != ""
        if remote_has:
            _git(["fetch", "origin", branch], site)
            _git(["checkout", "-B", branch, f"origin/{branch}"], site)
        else:
            _git(["checkout", "-B", branch], site, check=False)
        os.makedirs(os.path.join(site, "history"), exist_ok=True)
        shutil.copyfile(html_path, os.path.join(site, "index.html"))
        shutil.copyfile(html_path, os.path.join(site, "history", f"{date_str}.html"))
        open(os.path.join(site, ".nojekyll"), "a").close()
        _git(["add", "index.html", "history", ".nojekyll"], site)
        if _git(["diff", "--cached", "--quiet"], site, check=False).returncode == 0:
            log("  Page unchanged; nothing to publish")
            return
        _git(["-c", "user.name=CBB Edge", "-c", "user.email=cbb-edge@users.noreply.github.com",
              "commit", "-m", f"Update CBB board {now_et().strftime('%Y-%m-%d %H:%M')} ET"], site)
        r = _git(["push", "-u", "origin", branch], site, check=False)
        if r.returncode != 0:
            _git(["pull", "--rebase", "origin", branch], site, check=False)
            _git(["push", "-u", "origin", branch], site)
        m = re.search(r"github\.com[/:]([^/]+)/([^/.]+)", url)
        page = f"https://{m.group(1).lower()}.github.io/{m.group(2)}/" if m else url
        log(f"  Published: {page}")
    except Exception as e:
        log(f"  ! Publishing failed: {e}")
        log("    The dashboard was still written locally. See README > Publishing for sign-in help.")


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------
def main(argv=None):
    global OFFLINE
    ap = argparse.ArgumentParser(description="College basketball betting dashboard")
    ap.add_argument("--date", help="first day of the board, YYYY-MM-DD (default: today, US Eastern)")
    ap.add_argument("--days", type=int, default=CONFIG["days"], help="days to show (default 7)")
    ap.add_argument("--open", action="store_true", help="open the dashboard in your browser when done")
    ap.add_argument("--offline", action="store_true", help="rebuild from cached data only")
    ap.add_argument("--out", default=None, help="output HTML path")
    ap.add_argument("--no-publish", action="store_true", help="don't push to GitHub Pages")
    ap.add_argument("--no-odds", action="store_true", help="ignore sportsbook prices")
    ap.add_argument("--no-props", action="store_true", help="skip fetching player prop prices")
    ap.add_argument("--no-injuries", action="store_true", help="skip ESPN's injury report (rarely has college data)")
    args = ap.parse_args(argv)
    OFFLINE = args.offline
    root = os.path.join(HERE, CONFIG["data_dir"])
    for k, sub in (("root", ""), ("release", "release"), ("sb", "scoreboards"), ("games", "games"), ("misc", "misc")):
        DIRS[k] = os.path.join(root, sub)
        os.makedirs(DIRS[k], exist_ok=True)
    t0 = time.time()
    today = ddate(args.date) if args.date else now_et().date()
    log(f"CBB Edge: building the board for {today} + {args.days - 1} days")
    api = Api()
    db, _ = load_data(api, today)
    if not db.games:
        log("! No box scores loaded. Check your internet connection (and that pyarrow is installed), then run again.")
        return 1
    log(f"  {len(db.games)} games, {len(db.pbox)} player box scores loaded")
    slate, espn_days = load_slate(api, db, today, args.days)
    if args.no_odds:
        for g in slate:
            g["odds"] = None
    log(f"  {len(slate)} games on the slate ({espn_days} of {args.days} days from ESPN)")
    log("  Fitting team ratings, injuries and rosters ...")
    c = build_context(api, db, today, slate, no_injuries=args.no_injuries)
    props_book = {}
    if not args.no_props and not args.no_odds:
        pre = [g for g in slate if g["state"] == "pre" and g.get("odds")]
        if pre:
            with ThreadPoolExecutor(CONFIG["workers"]) as ex:
                for res in ex.map(lambda g: fetch_props(api, g["gid"], (g["odds"] or {}).get("prov")), pre):
                    props_book.update(res)
        log(f"  Player prop prices found: {len(props_book)}")
    log("  Modelling games ...")
    analyses = [analyze_game(c, g, props_book) for g in slate]
    top, gaps = pick_top_bets(c, analyses)
    watch = watch_list(c, analyses)
    pchecks = price_check_props(c, analyses)
    log_, tops = update_log(c, analyses, top)
    export_picks(tops, os.path.join(DIRS["root"], "picks.json"))
    summ = summarize_log(log_, tops)
    n_priced = sum(1 for ga in analyses if ga["sp_line"] is not None)
    log(f"  Sportsbook lines found for {n_priced} of {len(analyses)} games; {len(top)} top bets")
    alerts = []
    if espn_days < args.days and slate:
        alerts.append("ESPN's schedule couldn't be reached for some days, so those games come from the data release "
                      "schedule without lines or times. Run again later.")
    if n_priced == 0 and slate and not args.no_odds:
        alerts.append("No sportsbook lines were found, so there are no top bets yet. Model lines and the watch list "
                      "are still shown.")
    if c.n_cur_games < 1500:
        alerts.append(f"Early season: {c.n_cur_games} Division I games played so far, so team ratings still lean on "
                      "last season and roster moves. Expect bigger misses than usual until mid-December.")
    days = [(today + dt.timedelta(days=i)).isoformat() for i in range(args.days)]
    run_info = {"updated": now_et().strftime("%a %b %d, %I:%M %p ET").replace(" 0", " ")}
    html_ = render_page(c, analyses, top, gaps, watch, pchecks, summ, days, alerts, run_info)
    out = args.out or os.path.join(HERE, CONFIG["out"])
    with open(out, "w", encoding="utf-8") as f:
        f.write(html_)
    log(f"  Wrote {out} ({len(html_) // 1024} KB) in {time.time() - t0:.0f}s")
    if not args.no_publish and not args.offline:
        publish(out, today.isoformat())
    if args.open:
        webbrowser.open("file://" + os.path.abspath(out))
    return 0


if __name__ == "__main__":
    sys.exit(main())
