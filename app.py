"""
=============================================================
  WUMPUS WORLD - KNOWLEDGE-BASED AGENT
  Flask Web Application
  
  This file contains:
    1. Propositional Logic Engine (Literal, Clause, KB)
    2. Resolution Refutation Algorithm (AIMA Ch.7)
    3. Wumpus World Environment
    4. KB Agent (perceive → tell KB → ask KB → move)
    5. Flask REST API (game state, step, new game)
=============================================================
"""

from flask import Flask, jsonify, request, render_template
import random
import json

app = Flask(__name__)

# ─────────────────────────────────────────────────────────────
#  PART 1: PROPOSITIONAL LOGIC ENGINE
# ─────────────────────────────────────────────────────────────

class Literal:
    """
    A propositional literal — a variable with optional negation.
    
    Example:
        Literal("P_1_2")        →  P₁,₂  (pit at row=1, col=2)
        Literal("P_1_2", True)  → ¬P₁,₂  (no pit at row=1, col=2)
    """
    def __init__(self, name, negated=False):
        self.name    = name       # Variable name (string)
        self.negated = negated    # True means negated (¬)

    def negate(self):
        """Return the complement of this literal."""
        return Literal(self.name, not self.negated)

    def is_complement_of(self, other):
        """Returns True if this literal and 'other' are complements (p and ¬p)."""
        return self.name == other.name and self.negated != other.negated

    def __eq__(self, other):
        return self.name == other.name and self.negated == other.negated

    def __hash__(self):
        return hash((self.name, self.negated))

    def key(self):
        """Unique string key for set/dict use."""
        return ("-" if self.negated else "+") + self.name

    def __str__(self):
        return ("¬" if self.negated else "") + self.name

    def __repr__(self):
        return self.__str__()


class Clause:
    """
    A CNF Clause — a disjunction (OR) of literals.
    
    Example:
        Clause([P_1_2, P_2_1])  →  (P₁,₂ ∨ P₂,₁)
        Clause([])              →  □ (empty clause = contradiction)
    
    The clause is stored as a deduplicated frozenset for fast operations.
    """
    def __init__(self, literals=None):
        if literals is None:
            literals = []
        # Store as frozenset for deduplication and hashing
        self.literals = frozenset(literals)

    def is_empty(self):
        """Empty clause means contradiction — the whole proof collapses."""
        return len(self.literals) == 0

    def is_unit(self):
        """A unit clause has exactly one literal."""
        return len(self.literals) == 1

    def is_tautology(self):
        """
        A clause is a tautology if it contains both L and ¬L.
        Tautologies are always true and never help in resolution.
        """
        names_pos = set()
        names_neg = set()
        for lit in self.literals:
            (names_neg if lit.negated else names_pos).add(lit.name)
        return bool(names_pos & names_neg)  # Any overlap = tautology

    def key(self):
        """Canonical string key for deduplication."""
        return "|".join(sorted(lit.key() for lit in self.literals))

    def __hash__(self):
        return hash(self.key())

    def __eq__(self, other):
        return self.key() == other.key()

    def __str__(self):
        if self.is_empty():
            return "□"
        lits = sorted(str(l) for l in self.literals)
        if len(lits) == 1:
            return lits[0]
        return "(" + " ∨ ".join(lits) + ")"

    def __repr__(self):
        return self.__str__()


def pl_resolve(clause_a, clause_b):
    """
    Resolution Rule: Given two clauses that share a complementary literal,
    produce their resolvent (remove the complementary pair, merge the rest).
    
    Example:
        (A ∨ ¬B)  resolved with  (B ∨ C)
        on complement pair (¬B, B)
        → Result: (A ∨ C)
    
    Returns: list of resolvent clauses (usually 0 or 1)
    """
    resolvents = []

    for lit_a in clause_a.literals:
        for lit_b in clause_b.literals:

            # Found a complementary pair — resolve on it
            if lit_a.is_complement_of(lit_b):
                # Merge remaining literals (exclude the resolved pair)
                merged = (clause_a.literals - {lit_a}) | (clause_b.literals - {lit_b})
                resolvent = Clause(list(merged))

                # Skip tautologies (they're useless)
                if not resolvent.is_tautology():
                    resolvents.append(resolvent)

                return resolvents  # One pivot per resolution step

    return resolvents  # No complementary pair found


def pl_resolution_refutation(kb_clauses, query_literal, max_steps=600):
    """
    PL-RESOLUTION REFUTATION ALGORITHM (AIMA Algorithm 7.5)
    
    Goal: Prove that 'query_literal' is entailed by the KB.
    
    Strategy (Proof by Contradiction):
        1. Assume the OPPOSITE of what we want to prove (¬query)
        2. Add ¬query to the KB
        3. Apply resolution repeatedly
        4. If we derive □ (empty clause) → contradiction found
           → our assumption was WRONG → query IS entailed!  ✓
        5. If no new clauses can be derived → cannot prove it ✗
    
    Uses Set-of-Support strategy:
        - Only resolve clauses that trace back to ¬query
        - Much more efficient than resolving everything with everything
    
    Returns:
        dict with keys: proved (bool), steps (int), log (list of strings)
    """
    steps    = 0
    proof_log = []

    # Step 1: Negate the query to form our assumption
    neg_query_clause = Clause([query_literal.negate()])

    proof_log.append(f"GOAL: Prove {query_literal}")
    proof_log.append(f"ASSUMPTION (negation): {neg_query_clause}")
    proof_log.append(f"KB has {len(kb_clauses)} clauses")
    proof_log.append("─" * 50)

    # Step 2: Build working clause set = KB + ¬query
    clause_set = {}  # key → Clause

    def add_clause(c, source=""):
        if c.is_tautology():
            return False
        k = c.key()
        if k not in clause_set:
            clause_set[k] = c
            if source:
                proof_log.append(f"[ADD] {c}  ← {source}")
            return True
        return False

    for c in kb_clauses:
        add_clause(c)
    add_clause(neg_query_clause, "negated query (our assumption)")

    # Step 3: Set of Support starts with just {¬query}
    support   = [neg_query_clause]
    tried     = set()   # Pairs already attempted
    rounds    = 0
    MAX_ROUNDS = 30

    while rounds < MAX_ROUNDS:
        rounds += 1
        all_clauses    = list(clause_set.values())
        added_this_round = False

        for support_clause in list(support):
            for other_clause in all_clauses:

                if steps >= max_steps:
                    proof_log.append(f"[LIMIT] Reached max steps ({max_steps})")
                    return {"proved": False, "steps": steps, "log": proof_log}

                # Skip pairs we've already tried
                pair_key = tuple(sorted([support_clause.key(), other_clause.key()]))
                if pair_key in tried:
                    continue
                tried.add(pair_key)

                # Resolve the two clauses
                resolvents = pl_resolve(support_clause, other_clause)
                steps += 1

                for resolvent in resolvents:

                    # ★ EMPTY CLAUSE = CONTRADICTION = PROOF COMPLETE ★
                    if resolvent.is_empty():
                        proof_log.append(f"[STEP {steps}] {support_clause}")
                        proof_log.append(f"           ⊕ {other_clause}")
                        proof_log.append(f"           → □  ← CONTRADICTION!")
                        proof_log.append("─" * 50)
                        proof_log.append(f"✓ PROVED: {query_literal} is entailed by KB")
                        proof_log.append(f"✓ Steps used: {steps}")
                        return {"proved": True, "steps": steps, "log": proof_log}

                    if add_clause(resolvent, f"resolved from ⟨{support_clause}⟩ and ⟨{other_clause}⟩"):
                        support.append(resolvent)
                        added_this_round = True
                        proof_log.append(f"[STEP {steps}] {support_clause} ⊕ {other_clause} → {resolvent}")

                # Safety: stop if clause set explodes
                if len(clause_set) > 800:
                    proof_log.append(f"[LIMIT] Too many clauses ({len(clause_set)})")
                    return {"proved": False, "steps": steps, "log": proof_log}

        # If nothing new was added this round, we're done
        if not added_this_round:
            proof_log.append("─" * 50)
            proof_log.append(f"✗ No new clauses. Cannot prove {query_literal}")
            break

    return {"proved": False, "steps": steps, "log": proof_log}


# ─────────────────────────────────────────────────────────────
#  PART 2: KNOWLEDGE BASE
# ─────────────────────────────────────────────────────────────

class KnowledgeBase:
    """
    The agent's belief system — stores all known facts as CNF clauses.
    
    Two main operations:
        TELL(clause) — add a new fact/rule to the KB
        ASK(literal) — query whether the literal is provable
    """
    def __init__(self):
        self.clauses     = []         # All CNF clauses
        self._keys       = set()      # For deduplication
        self.total_steps = 0          # Cumulative inference steps
        self._unit_facts = {}         # Fast lookup: name → negated

    def tell(self, clause):
        """Add a clause to the KB (no duplicates, no tautologies)."""
        if clause.is_tautology():
            return
        k = clause.key()
        if k not in self._keys:
            self._keys.add(k)
            self.clauses.append(clause)
            # Index unit clauses for O(1) lookup
            if clause.is_unit():
                lit = next(iter(clause.literals))
                self._unit_facts[lit.name] = lit.negated

    def tell_all(self, clauses):
        """Add multiple clauses at once."""
        for c in clauses:
            self.tell(c)

    def tell_fact(self, name, negated=False):
        """Shorthand: assert a single literal as a fact."""
        self.tell(Clause([Literal(name, negated)]))

    def is_direct_fact(self, literal):
        """O(1) check: is this literal directly in KB as a unit clause?"""
        return (literal.name in self._unit_facts and
                self._unit_facts[literal.name] == literal.negated)

    def ask(self, literal):
        """
        Ask whether 'literal' is entailed by the KB.
        
        First tries fast unit-clause lookup.
        Falls back to full resolution refutation.
        """
        # Fast path: directly known
        if self.is_direct_fact(literal):
            return {
                "proved": True, "steps": 0,
                "method": "direct-fact",
                "log": [f"[FAST] {literal} is a direct KB fact"]
            }

        # Full resolution
        result = pl_resolution_refutation(self.clauses, literal)
        self.total_steps += result["steps"]
        result["method"] = "resolution"
        return result

    @property
    def size(self):
        return len(self.clauses)

    def recent_clauses_str(self, n=20):
        """Return the last n clauses as a readable string."""
        return [str(c) for c in self.clauses[-n:]]


# ─────────────────────────────────────────────────────────────
#  PART 3: WUMPUS WORLD ENVIRONMENT
# ─────────────────────────────────────────────────────────────

class WumpusWorld:
    """
    The Wumpus World grid environment.
    
    Layout rules:
        - Agent always starts at (row=0, col=0)
        - Pits are randomly placed (not at start)
        - One Wumpus is randomly placed (not at start)
        - One Gold piece is randomly placed (not at start)
    
    Percept rules:
        - BREEZE  if any adjacent cell has a Pit
        - STENCH  if any adjacent cell has the Wumpus (alive)
        - GLITTER if the current cell has Gold
    """
    def __init__(self, rows, cols, num_pits):
        self.rows     = rows
        self.cols     = cols
        self.num_pits = num_pits

        # Initialize grid — each cell is a dict of properties
        self.grid = [
            [{"pit": False, "wumpus": False, "gold": False} for _ in range(cols)]
            for _ in range(rows)
        ]

        # Agent state
        self.agent_row   = 0
        self.agent_col   = 0
        self.agent_alive = True
        self.gold_found  = False
        self.wumpus_alive = True

        # Track hazard positions (revealed when agent dies or wins)
        self.pit_positions    = []
        self.wumpus_pos       = None
        self.gold_pos         = None

        self._place_hazards()

    def _place_hazards(self):
        """Randomly place pits, wumpus, and gold — never at (0,0)."""
        all_cells = [(r, c) for r in range(self.rows) for c in range(self.cols)
                     if not (r == 0 and c == 0)]
        random.shuffle(all_cells)

        # Place Wumpus
        wr, wc = all_cells.pop()
        self.grid[wr][wc]["wumpus"] = True
        self.wumpus_pos = (wr, wc)

        # Place Gold
        gr, gc = all_cells.pop()
        self.grid[gr][gc]["gold"] = True
        self.gold_pos = (gr, gc)

        # Place Pits
        actual_pits = min(self.num_pits, len(all_cells))
        for _ in range(actual_pits):
            pr, pc = all_cells.pop()
            self.grid[pr][pc]["pit"] = True
            self.pit_positions.append((pr, pc))

    def get_adjacent(self, row, col):
        """Return list of valid adjacent cell coordinates (4-connected)."""
        adjacent = []
        if row > 0:             adjacent.append((row - 1, col))
        if row < self.rows - 1: adjacent.append((row + 1, col))
        if col > 0:             adjacent.append((row, col - 1))
        if col < self.cols - 1: adjacent.append((row, col + 1))
        return adjacent

    def get_percepts(self, row, col):
        """
        Compute percepts at (row, col):
            - Breeze  if any neighbor has a pit
            - Stench  if any neighbor has the (alive) wumpus
            - Glitter if this cell has gold
        """
        breeze  = False
        stench  = False
        glitter = self.grid[row][col]["gold"]

        for r, c in self.get_adjacent(row, col):
            if self.grid[r][c]["pit"]:
                breeze = True
            if self.grid[r][c]["wumpus"] and self.wumpus_alive:
                stench = True

        return {"breeze": breeze, "stench": stench, "glitter": glitter}

    def move_agent(self, row, col):
        """
        Move agent to (row, col).
        Returns a result dict with what happened.
        """
        self.agent_row = row
        self.agent_col = col
        cell = self.grid[row][col]

        hit_pit    = cell["pit"]
        hit_wumpus = cell["wumpus"] and self.wumpus_alive
        died       = hit_pit or hit_wumpus

        got_gold = cell["gold"] and not self.gold_found
        if got_gold:
            self.gold_found = True
        if hit_wumpus:
            self.wumpus_alive = False

        return {
            "died":     died,
            "got_gold": got_gold,
            "cause":    "Pit" if hit_pit else ("Wumpus" if hit_wumpus else None)
        }


# ─────────────────────────────────────────────────────────────
#  PART 4: KNOWLEDGE-BASED AGENT
# ─────────────────────────────────────────────────────────────

class KBAgent:
    """
    The Knowledge-Based Agent that navigates the Wumpus World.
    
    Core loop (each step):
        1. PERCEIVE current cell → get Breeze, Stench, Glitter
        2. TELL KB → encode percepts as CNF clauses
        3. ASK KB  → run resolution to find safe neighbors
        4. MOVE    → step into a proven-safe cell
    
    Decision priority:
        1. Move to unvisited safe neighbor (proven by KB)
        2. BFS through visited cells to reach any safe unvisited cell
        3. Backtrack to visited neighbor (explore further later)
        4. Take a risk if completely stuck (last resort)
    """
    def __init__(self, world):
        self.world    = world
        self.kb       = KnowledgeBase()
        self.moves    = 0
        self.visited  = set()     # Cells the agent has been to
        self.no_pit   = set()     # Cells proven pit-free
        self.no_wumpus= set()     # Cells proven wumpus-free
        self.unsafe   = set()     # Confirmed dangerous cells
        self.status   = "alive"   # "alive" | "dead" | "won" | "stuck"
        self.done     = False

        # History for the dashboard log
        self.step_log = []

        # Initialize: (0,0) is always safe
        self._mark_safe(0, 0)
        self.kb.tell_fact("P_0_0", negated=True)   # No pit at start
        self.kb.tell_fact("W_0_0", negated=True)   # No wumpus at start

        # First perception
        self.visited.add("0,0")
        self._perceive(0, 0)

        self._log("info", "Agent initialized at (0,0). KB seeded with start safety.")

    def _key(self, r, c):
        return f"{r},{c}"

    def _mark_safe(self, r, c):
        """Mark cell as proven safe (both pit-free and wumpus-free)."""
        self.no_pit.add(self._key(r, c))
        self.no_wumpus.add(self._key(r, c))

    def is_safe(self, r, c):
        """Is this cell proven safe by KB?"""
        k = self._key(r, c)
        return k in self.no_pit and k in self.no_wumpus

    def _log(self, level, msg):
        """Add entry to step log (shown in dashboard)."""
        self.step_log.append({"level": level, "msg": msg})
        # Keep only last 200 entries
        if len(self.step_log) > 200:
            self.step_log.pop(0)

    def _perceive(self, r, c):
        """
        TELL KB about the percepts at (r, c).
        
        Encodes the Wumpus World axioms into CNF:
        
          Breeze(r,c) ↔ ∃ neighbor n: Pit(n)
        
          In CNF:
            If breeze:   P_n1 ∨ P_n2 ∨ ...        (at least one neighbor is a pit)
            If no breeze: ¬P_n for all n            (all neighbors pit-free)
        
          Same pattern for Stench ↔ Wumpus.
        """
        percepts = self.world.get_percepts(r, c)
        neighbors = self.world.get_adjacent(r, c)
        
        self._log("percept", f"At ({r},{c}): {'Breeze ' if percepts['breeze'] else ''}{'Stench ' if percepts['stench'] else ''}{'Glitter' if percepts['glitter'] else 'None'}")

        # ── BREEZE ENCODING ──────────────────────────────────
        if percepts["breeze"]:
            # B(r,c) is TRUE
            self.kb.tell_fact(f"B_{r}_{c}")

            # At least one neighbor must be a pit
            pit_lits = [Literal(f"P_{nr}_{nc}") for nr, nc in neighbors]
            if pit_lits:
                self.kb.tell(Clause(pit_lits))           # P_n1 ∨ P_n2 ∨ ...

            # Biconditional: B → (P_n1 ∨ ...) as ¬B ∨ P_n1 ∨ ...
            if pit_lits:
                self.kb.tell(Clause([Literal(f"B_{r}_{c}", negated=True)] + pit_lits))

        else:
            # No breeze → no adjacent pit for ANY neighbor
            self.kb.tell_fact(f"B_{r}_{c}", negated=True)
            for nr, nc in neighbors:
                self.kb.tell_fact(f"P_{nr}_{nc}", negated=True)
                self.no_pit.add(self._key(nr, nc))
                self._log("safe", f"  No breeze → cell ({nr},{nc}) is pit-free")

        # ── STENCH ENCODING ──────────────────────────────────
        if percepts["stench"]:
            self.kb.tell_fact(f"S_{r}_{c}")

            wumpus_lits = [Literal(f"W_{nr}_{nc}") for nr, nc in neighbors]
            if wumpus_lits:
                self.kb.tell(Clause(wumpus_lits))        # W_n1 ∨ W_n2 ∨ ...

            if wumpus_lits:
                self.kb.tell(Clause([Literal(f"S_{r}_{c}", negated=True)] + wumpus_lits))

        else:
            # No stench → no adjacent wumpus
            self.kb.tell_fact(f"S_{r}_{c}", negated=True)
            for nr, nc in neighbors:
                self.kb.tell_fact(f"W_{nr}_{nc}", negated=True)
                self.no_wumpus.add(self._key(nr, nc))

        # ── BICONDITIONAL SUPPORT (contrapositive) ───────────
        # Pit at neighbor implies breeze here: P_n → B(r,c) = ¬P_n ∨ B(r,c)
        for nr, nc in neighbors:
            self.kb.tell(Clause([Literal(f"P_{nr}_{nc}", negated=True),
                                  Literal(f"B_{r}_{c}")]))
            self.kb.tell(Clause([Literal(f"W_{nr}_{nc}", negated=True),
                                  Literal(f"S_{r}_{c}")]))

    def infer_safe(self, r, c):
        """
        ASK KB: Is cell (r,c) safe?
        
        Runs Resolution Refutation twice:
            1. Prove ¬P(r,c) — no pit here
            2. Prove ¬W(r,c) — no wumpus here
        
        Returns dict: { safe, total_steps, log }
        """
        key = self._key(r, c)

        if self.is_safe(r, c):
            return {"safe": True, "total_steps": 0, "method": "cached"}

        if key in self.unsafe:
            return {"safe": False, "total_steps": 0, "method": "cached-unsafe"}

        total_steps = 0
        inf_log = []

        # ── Prove ¬P(r,c) ────────────────────────────────────
        no_pit_proven = key in self.no_pit
        if not no_pit_proven:
            inf_log.append(f"ASK: Prove ¬P_{r}_{c} (no pit at ({r},{c}))")
            result = self.kb.ask(Literal(f"P_{r}_{c}", negated=True))
            total_steps += result["steps"]
            inf_log.extend(result.get("log", []))

            if result["proved"]:
                self.no_pit.add(key)
                no_pit_proven = True
                self._log("proof", f"  Proved: No pit at ({r},{c}) [{result['steps']} steps]")
            else:
                # Maybe pit IS proven?
                r2 = self.kb.ask(Literal(f"P_{r}_{c}"))
                total_steps += r2["steps"]
                if r2["proved"]:
                    self.unsafe.add(key)
                    self._log("danger", f"  Confirmed: PIT at ({r},{c})!")
                return {"safe": False, "total_steps": total_steps, "log": inf_log}

        # ── Prove ¬W(r,c) ────────────────────────────────────
        no_wumpus_proven = key in self.no_wumpus
        if not no_wumpus_proven:
            inf_log.append(f"ASK: Prove ¬W_{r}_{c} (no wumpus at ({r},{c}))")
            result = self.kb.ask(Literal(f"W_{r}_{c}", negated=True))
            total_steps += result["steps"]
            inf_log.extend(result.get("log", []))

            if result["proved"]:
                self.no_wumpus.add(key)
                no_wumpus_proven = True
                self._log("proof", f"  Proved: No wumpus at ({r},{c}) [{result['steps']} steps]")
            else:
                r2 = self.kb.ask(Literal(f"W_{r}_{c}"))
                total_steps += r2["steps"]
                if r2["proved"]:
                    self.unsafe.add(key)
                    self._log("danger", f"  Confirmed: WUMPUS at ({r},{c})!")
                return {"safe": False, "total_steps": total_steps, "log": inf_log}

        safe = no_pit_proven and no_wumpus_proven
        return {"safe": safe, "total_steps": total_steps, "log": inf_log}

    def _choose_move(self):
        """
        Decide the next cell to move to.
        
        Priority:
            1. Unvisited, safe neighbor (best case)
            2. BFS to any reachable, safe, unvisited cell
            3. Backtrack to a visited safe neighbor
            4. Risky move (unknown cell — last resort)
        """
        r, c    = self.world.agent_row, self.world.agent_col
        neighbors = self.world.get_adjacent(r, c)

        fresh_safe   = []   # Safe + unvisited neighbors
        visited_safe = []   # Safe + visited neighbors
        risky        = []   # Unknown risk neighbors

        for nr, nc in neighbors:
            key = self._key(nr, nc)
            if key in self.unsafe:
                continue

            result = self.infer_safe(nr, nc)

            if result["safe"]:
                if key not in self.visited:
                    fresh_safe.append((nr, nc, "explore-safe"))
                else:
                    visited_safe.append((nr, nc, "backtrack"))
            else:
                if key not in self.unsafe:
                    risky.append((nr, nc, "risky"))

        # Priority 1: Fresh safe neighbor
        if fresh_safe:
            return fresh_safe[0]

        # Priority 2: BFS to find reachable unvisited safe cell
        bfs_target = self._bfs_find_target()
        if bfs_target:
            first_step = self._bfs_first_step(r, c, bfs_target[0], bfs_target[1])
            if first_step:
                return (first_step[0], first_step[1], "bfs-navigate")

        # Priority 3: Backtrack
        if visited_safe:
            return visited_safe[0]

        # Priority 4: Risk it
        if risky:
            self._log("warn", "No safe move found — taking a risk!")
            return risky[0]

        return None  # Completely stuck

    def _bfs_find_target(self):
        """BFS: find nearest unvisited+safe cell reachable via safe path."""
        start = (self.world.agent_row, self.world.agent_col)
        queue = [start]
        seen  = {self._key(*start)}

        while queue:
            r, c = queue.pop(0)
            for nr, nc in self.world.get_adjacent(r, c):
                key = self._key(nr, nc)
                if key in seen or key in self.unsafe:
                    continue
                seen.add(key)
                if key not in self.visited and self.is_safe(nr, nc):
                    return (nr, nc)
                if key in self.visited:
                    queue.append((nr, nc))

        return None

    def _bfs_first_step(self, from_r, from_c, to_r, to_c):
        """BFS: find the FIRST step on shortest path from source to target."""
        from collections import deque
        queue  = deque([(from_r, from_c)])
        parent = {}
        seen   = {self._key(from_r, from_c)}

        while queue:
            r, c = queue.popleft()
            for nr, nc in self.world.get_adjacent(r, c):
                key = self._key(nr, nc)
                if key in seen or key in self.unsafe:
                    continue
                seen.add(key)
                parent[key] = (r, c)

                if nr == to_r and nc == to_c:
                    # Trace back to find first step
                    cur = (to_r, to_c)
                    while True:
                        p = parent.get(self._key(*cur))
                        if p is None:
                            break
                        if p == (from_r, from_c):
                            return cur
                        cur = p
                    return cur

                if self._key(nr, nc) in self.visited or self.is_safe(nr, nc):
                    queue.append((nr, nc))

        return None

    def tick(self):
        """
        Execute ONE agent step.
        Returns a dict describing what happened (used by API).
        """
        if self.done:
            return None

        move = self._choose_move()

        if move is None:
            self.done   = True
            self.status = "stuck"
            self._log("error", "AGENT STUCK — no safe moves available!")
            return {"type": "stuck", "step": self.moves}

        nr, nc, move_type = move

        # Execute the move in the world
        result = self.world.move_agent(nr, nc)
        self.moves += 1
        self.visited.add(self._key(nr, nc))

        self._log("move", f"Move #{self.moves}: → ({nr},{nc}) [{move_type}]")

        if result["died"]:
            # Confirm the hazard in KB
            cause = result["cause"]
            self.unsafe.add(self._key(nr, nc))
            if cause == "Pit":
                self.kb.tell_fact(f"P_{nr}_{nc}")
            elif cause == "Wumpus":
                self.kb.tell_fact(f"W_{nr}_{nc}")
            self.done   = True
            self.status = "dead"
            self._log("error", f"AGENT DIED at ({nr},{nc}) — {cause}!")
            return {"type": "died", "r": nr, "c": nc, "cause": cause, "step": self.moves}

        # Safe arrival — perceive and update KB
        self._perceive(nr, nc)

        if result["got_gold"]:
            self.done   = True
            self.status = "won"
            self._log("win", f"GOLD FOUND at ({nr},{nc})! Mission complete in {self.moves} moves!")
            return {"type": "won", "r": nr, "c": nc, "step": self.moves,
                    "percepts": self.world.get_percepts(nr, nc)}

        return {
            "type": "moved",
            "r": nr, "c": nc,
            "move_type": move_type,
            "step": self.moves,
            "percepts": self.world.get_percepts(nr, nc)
        }

    @property
    def safe_count(self):
        """How many cells are proven safe (pit-free AND wumpus-free)?"""
        return len(self.no_pit & self.no_wumpus)

    def get_full_state(self):
        """
        Serialize the complete game state for the frontend.
        Returns a JSON-serializable dict.
        """
        world = self.world
        grid  = []

        for r in range(world.rows):
            row_data = []
            for c in range(world.cols):
                key      = self._key(r, c)
                cell     = world.grid[r][c]
                percepts = world.get_percepts(r, c)

                is_agent   = (r == world.agent_row and c == world.agent_col and self.status != "dead")
                is_visited = key in self.visited
                is_safe    = self.is_safe(r, c)
                is_unsafe  = key in self.unsafe

                # Only reveal hazards if game is over OR cell was visited
                reveal = (self.done or is_visited)

                row_data.append({
                    "r": r, "c": c,
                    "is_agent":   is_agent,
                    "is_visited": is_visited,
                    "is_safe":    is_safe,
                    "is_unsafe":  is_unsafe,
                    "has_pit":    cell["pit"]    if reveal else False,
                    "has_wumpus": cell["wumpus"] if reveal else False,
                    "has_gold":   cell["gold"]   if (reveal or cell["gold"] and self.done) else False,
                    "breeze":     percepts["breeze"]  if is_visited else False,
                    "stench":     percepts["stench"]  if is_visited else False,
                    "glitter":    percepts["glitter"] if is_visited else False,
                })
            grid.append(row_data)

        # Current cell percepts
        cur_percepts = world.get_percepts(world.agent_row, world.agent_col)

        return {
            "grid":          grid,
            "rows":          world.rows,
            "cols":          world.cols,
            "agent_row":     world.agent_row,
            "agent_col":     world.agent_col,
            "agent_status":  self.status,
            "done":          self.done,
            "moves":         self.moves,
            "kb_size":       self.kb.size,
            "inf_steps":     self.kb.total_steps,
            "safe_count":    self.safe_count,
            "visited_count": len(self.visited),
            "unsafe_count":  len(self.unsafe),
            "frontier_count":max(0, self.safe_count - len(self.visited)),
            "current_percepts": cur_percepts,
            "kb_recent":     self.kb.recent_clauses_str(20),
            "step_log":      self.step_log[-50:],
        }


# ─────────────────────────────────────────────────────────────
#  PART 5: FLASK API ROUTES
# ─────────────────────────────────────────────────────────────

# Global game instance (one game per server session)
game_agent = None


@app.route("/")
def index():
    """Serve the main game dashboard."""
    return render_template("index.html")


@app.route("/api/new_game", methods=["POST"])
def new_game():
    """
    Start a new game.
    
    POST body (JSON):
        rows:     number of rows (3-8)
        cols:     number of columns (3-8)
        num_pits: number of pits (1-10)
    """
    global game_agent
    data = request.get_json() or {}

    rows     = max(3, min(8,  int(data.get("rows",     4))))
    cols     = max(3, min(8,  int(data.get("cols",     4))))
    num_pits = max(1, min(10, int(data.get("num_pits", 3))))

    world      = WumpusWorld(rows, cols, num_pits)
    game_agent = KBAgent(world)

    return jsonify({"success": True, "state": game_agent.get_full_state()})


@app.route("/api/step", methods=["POST"])
def step():
    """Execute one agent step and return the new state."""
    global game_agent
    if game_agent is None:
        return jsonify({"error": "No game active. Start a new game first."}), 400

    result = game_agent.tick()
    state  = game_agent.get_full_state()
    state["last_action"] = result

    return jsonify({"success": True, "state": state, "result": result})


@app.route("/api/state", methods=["GET"])
def get_state():
    """Get the current game state without advancing."""
    global game_agent
    if game_agent is None:
        return jsonify({"no_game": True})
    return jsonify({"success": True, "state": game_agent.get_full_state()})


@app.route("/api/reveal", methods=["GET"])
def reveal():
    """Reveal the full grid (for debugging / game over screen)."""
    global game_agent
    if game_agent is None:
        return jsonify({"error": "No game active"}), 400
    game_agent.done = True  # Force full reveal
    return jsonify({"success": True, "state": game_agent.get_full_state()})


if __name__ == "__main__":
    print("=" * 55)
    print("  WUMPUS WORLD — Knowledge-Based Agent")
    print("  Visit: http://localhost:5000")
    print("=" * 55)
    app.run(debug=True, port=5000)
