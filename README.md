# Wumpus World — Knowledge-Based Agent (Web App)
**FAST-NUCES AI Lab | Question 6 — Coding Project**

A fully functional web-based Wumpus World simulator with:
- ✅ Propositional Logic KB (TELL / ASK)
- ✅ Resolution Refutation Algorithm (AIMA Ch.7)
- ✅ Dynamic grid sizing (3×3 to 8×8)
- ✅ Random hazard placement every episode
- ✅ Real-time percept generation (Breeze, Stench, Glitter)
- ✅ Beautiful dashboard UI
- ✅ Step-by-step inference log

---

## Project Structure

```
wumpus_app/
│
├── app.py               ← Flask backend (ALL game logic here)
│   ├── Literal          ← Propositional literal
│   ├── Clause           ← CNF clause (disjunction)
│   ├── pl_resolve()     ← Resolution rule
│   ├── pl_resolution()  ← Full refutation algorithm
│   ├── KnowledgeBase    ← TELL / ASK interface
│   ├── WumpusWorld      ← Environment (grid, hazards, percepts)
│   └── KBAgent          ← Perceive → Tell → Ask → Move
│
├── templates/
│   └── index.html       ← Dashboard UI (HTML + CSS + JS)
│
├── requirements.txt     ← Python dependencies
└── README.md            ← This file
```

---

## Setup & Run (Local)

```bash
# 1. Go into the project folder
cd wumpus_app

# 2. Install dependencies
pip install -r requirements.txt

# 3. Run the server
python app.py

# 4. Open browser
# Visit: http://localhost:5000
```

---

## Deploy to Render (Free Hosting)

1. Push this folder to a GitHub repo.
2. Go to [render.com](https://render.com) → New Web Service.
3. Connect your GitHub repo.
4. Set:
   - **Build Command:** `pip install -r requirements.txt`
   - **Start Command:**  `gunicorn app:app`
5. Click **Deploy**. Your app goes live in ~2 minutes!

Add `gunicorn` to requirements.txt for Render:
```
flask==3.0.0
gunicorn==21.2.0
```

---

## How the Logic Works

### TELL (Encoding Percepts as CNF)

When agent is at (r,c) and senses Breeze:
```
Breeze(r,c) ↔ Pit(r-1,c) ∨ Pit(r+1,c) ∨ Pit(r,c-1) ∨ Pit(r,c+1)
```
Added to KB as CNF clauses:
- `(Pit_r-1_c ∨ Pit_r+1_c ∨ ...)` — at least one neighbor is a pit
- `(¬Breeze_r_c ∨ Pit_n1 ∨ ...)` — biconditional left side
- `(¬Pit_n ∨ Breeze_r_c)` for each n — biconditional right side

When NO Breeze:
- `¬Pit_n` for each neighbor (very powerful — eliminates possibilities!)

### ASK (Resolution Refutation)

To prove cell (x,y) is safe, prove `¬Pit(x,y)` AND `¬Wumpus(x,y)`:

1. Assume the OPPOSITE: add `Pit(x,y)` as a clause
2. Apply resolution on KB ∪ {Pit(x,y)}
3. If we derive □ (empty clause) → contradiction → `¬Pit(x,y)` is TRUE ✓
4. If no contradiction → cannot prove safety ✗

### Agent Decision

Priority order:
1. Move to unvisited + proven-safe neighbor (best)
2. BFS to any reachable safe unvisited cell
3. Backtrack through visited safe cells
4. Risky move if completely stuck (last resort)

---

## API Endpoints

| Method | URL           | Description                    |
|--------|---------------|--------------------------------|
| GET    | `/`           | Serve the dashboard            |
| POST   | `/api/new_game` | Start new game (rows/cols/pits) |
| POST   | `/api/step`   | Execute one agent step         |
| GET    | `/api/state`  | Get current state (no advance) |
| GET    | `/api/reveal` | Reveal entire grid             |

---

## Keyboard Shortcuts

| Key       | Action            |
|-----------|-------------------|
| `N`       | New Game          |
| `SPACE`   | Toggle Auto-Play  |
| `S`       | Step Once         |
