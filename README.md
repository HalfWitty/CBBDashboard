# CBB Edge

One Python script pulls men's college basketball data from free public sources, models
every Division I game for the next 7 days, and writes `cbb_dashboard.html`. After each run
it publishes the page to GitHub Pages: **https://halfwitty.github.io/CBBDashboard/**

## Setup (once)

```
pip install requests numpy pyarrow
```

Python 3.9 or newer. Git is needed for publishing (same sign-in as your NBA and NHL boards).

Put a copy of `edge_common.py` (the same helper your NBA, NHL and NFL boards use) in the
same folder as `cbb_edge.py`. It adds letter grades, trend picks, suggested units and the
Track record scatter. College trend settings are set inside `cbb_edge.py`, so the helper
file stays identical in every folder.

## Run

```
python cbb_edge.py
```

That builds the board and publishes it. Add `--open` to also open it in your browser.

- The **first run** downloads two seasons of box scores (about 9 MB) and fills in recent
  closing lines from ESPN game summaries. Expect a few minutes.
- After that, each run only pulls what's new.
- Data is cached in `cbb_data/` next to the script. Delete that folder to start fresh
  (this also clears the track record).

College lines mostly go up the day before each game, so run it once a day (afternoon is
best) to pick up the next day's lines.

Options:

| Flag | What it does |
|---|---|
| `--open` | Open the dashboard in your browser when done |
| `--days 3` | Show fewer or more days (default 7) |
| `--date 2026-11-12` | Build the board starting on another date |
| `--no-publish` | Build locally without pushing to GitHub |
| `--offline` | Rebuild from cached data without downloading |
| `--no-odds` | Ignore sportsbook prices |
| `--no-props` | Skip fetching player prop prices |
| `--out path.html` | Write the dashboard somewhere else |

## What's on the dashboard

- **Top bets**: graded A-D with suggested units, then trend picks (situational factors
  like record, margin, form, home/road and streaks, each with its record in past games;
  they start once teams have played 4 games). The best bets of the week across spreads, moneylines and totals (and
  props when the feed has prices), grouped by day, each with a price bar showing where
  it's a deal, thin or a pass, with the book's price marked. Below that: model lines for
  games without a line yet (and the number to bet each side at), props to price-check,
  and big model vs market gaps to investigate.
- **Games**: every Division I game, by day. Search for a team (searches the whole week),
  or filter to games with a line, games with a value bet, ranked teams, or one
  conference. Open a game for:
  - how to bet it: side, moneyline, total and props in plain language
  - the betting board: moneyline, spread, total, team totals and 1st half, each with our
    probability, the market's, fair odds and a "bet at" price; type your book's price
    (and line) to see the expected return
  - who's missing, projected minutes and player projections (points, rebounds, assists,
    threes, PRA)
  - form: last 5, record by home / road / neutral, conference record and standing,
    against the spread, over/under, rest, roster change since last season, head to head
  - about 20 stats with ranks out of 365
- **Props**: players expected to play 18+ minutes, any stat, with a calculator for any
  line and price.
- **Who's missing**: college programs don't publish injury reports, so this lists
  rotation players who missed their team's recent games.
- **Rankings**: the model's top 75 and every conference's standings.
- **Track record** and **How it works**.

## How good is it?

Tested day by day through 2025-26 (no hindsight) against 1,454 DraftKings closing lines:

- Margins: the model alone missed by 11.3 points (root mean square) vs 11.0 for the
  closing spread; blending the two beat the line alone.
- The pick rule the board uses went 127-102 on spreads (55.5%, +7.3% per bet) and
  +4.2% on moneylines at closing prices. Those settings were chosen on the same games,
  so expect real results to be thinner.
- Totals: the market was better than the model, so totals rarely make the list.
- When the model disagreed with the spread by 6+ points it went 19-25, so those games
  are flagged as warnings instead of picks.

Early in the season (until about mid-December) ratings lean on last season and roster
moves, so expect bigger misses. Watch the Track record tab before trusting any market.

## Publishing to GitHub Pages (one-time setup)

1. Create an empty public repository named **CBBDashboard** on GitHub.
2. Run the script once. It clones the repo into `cbb_site/` next to the script and
   pushes `index.html`.
3. On GitHub: repo **Settings -> Pages -> Build and deployment**: Source "Deploy from a
   branch", branch `main`, folder `/ (root)`, Save.

After that, every run updates the page within a minute or two. Each day's board is also
kept at `history/YYYY-MM-DD.html`. Use `--no-publish` to skip pushing, or set
`"repo_url": ""` in `CONFIG` to turn publishing off. Only the dashboard is published;
your cached data and prediction log stay on your computer.

## Tuning

Settings are in `CONFIG` at the top of `cbb_edge.py`: `hl_days` (how fast form fades),
`prior_games`, `prior_regress` and `roster_shift_w` (how much last season and roster
moves count), `w_model_margin` / `w_model_total` (model vs market blend),
`max_gap_pts` (the disagreement cap), and for top bets `top_bets_max`, `min_ev_top`,
`buffer_main`, `buffer_total`.

## Data sources

- Box scores and schedules: ESPN, via the sportsdataverse data releases on GitHub
  (`sportsdataverse/sportsdataverse-data`), topped up from ESPN game summaries
- Schedule, lines, AP rankings, rosters, prop prices: ESPN's public API

If a run prints "Sportsbook lines found for 0 of N games" while lines are posted, send the
files in `cbb_data/scoreboards` so the parser can be adjusted.

## Before you bet

Suspensions, illnesses and players sitting aren't known until they miss a game. College
lines move a lot; get the best number you can. Nothing here is financial advice. Bet only
what you can afford to lose.
