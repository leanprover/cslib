import Std.Data.HashMap

namespace GaleShapley101

variable (α β : Type) [Inhabited α] [Inhabited β]
 [BEq α] [BEq β] [Hashable α] [Hashable β]
 [ToString α] [ToString β]

structure Candidate where
  id          : α
  preferences : List β
deriving Repr, Inhabited

structure Post where
  id          : β
  capacity    : Nat
  preferences : List α
deriving Repr, Inhabited

structure Instance where
  candidates : List $ Candidate α β
  posts : List $ Post α β
deriving Repr

abbrev Matching := List (α × β)

structure PostState where
  assignments : List $ Candidate α β
  capacity : Nat
  rank : Candidate α β → Nat
deriving Inhabited

abbrev States := Std.HashMap β (PostState α β)

abbrev GS := StateT (States α β) Id

variable {α β}

/- initialize states for all posts -/

def makeRank (prefList : List α) : Candidate α β → Nat :=
  let d0 := Std.HashMap.emptyWithCapacity 10000
  let d1 := d0.insertMany $ prefList.zipIdx
  fun c => d1.get! c.id

def initState (inst : Instance α β) : @States α β _ _ :=
  let data := Std.HashMap.emptyWithCapacity 10000
  data.insertMany $
   inst.posts.map fun p =>
    let r := makeRank p.preferences
    (p.id, { assignments := [], capacity := p.capacity, rank := r })


def propose (c : Candidate α β) (w : PostState α β)
 : Option (Candidate α β) × PostState α β :=
  if w.assignments.length < w.capacity then
    -- Post has space, accept candidate
    (none, { w with assignments := c :: w.assignments })
  else
    -- full, check if new candidate is better than worst assignment
    match w.assignments.getLast? with
    | none =>
      -- should not happen
      (none, { w with assignments := [c] })
    | some worst =>
      if w.rank c < w.rank worst then
        let na := (c :: w.assignments.dropLast).mergeSort
          (fun a b => w.rank a < w.rank b)
        (some worst, { w with assignments := na })
      else
        (some c, w)


partial def proposals (free : List $ Candidate α β) : (GS α β) Unit := do
  match free with
  | [] => return ()  -- base case: no more free candidates
  | c :: cs =>
    if c.preferences.isEmpty then
      -- candidate exhausted all preferences, remains unmatched
      dbg_trace s!"{c.id}/{c.preferences.length} ignored ({free.length})"
      proposals cs
    else
      -- candidate proposes to most preferred post
      let postId := c.preferences.head!
      let states ← get
      let postState := states.get! postId
      dbg_trace s!"{c.id}/{c.preferences.length} -> {postId}/{postState.assignments.length} ({free.length})"

      -- make proposal using the pure propose function
      let (rejected, newPostState) := propose c postState
      let newStates := states.insert postId newPostState
      set newStates

      -- continue with remaining candidates plus any rejected candidate
      match rejected with
      | none => proposals cs
      | some r =>
        let u := { r with preferences := r.preferences.tail! }
        proposals (u :: cs)


-- Run proposals and return final state
def runProposals (cs : List (Candidate α β)) (init : States α β)
 : States α β :=
 (proposals cs).run init |>.snd


-- Extract final matching from states
def getMatching (states : States α β) : Matching α β :=
  states.toList.flatMap fun (p, ps) =>
    ps.assignments.map fun c => (c.id, p)

-- Main stable matching function
def stableMatching (inst : Instance α β) : Matching α β :=
  getMatching (runProposals inst.candidates (initState inst))


-- Example with posts having different capacities
def exampleInstance : Instance Nat Nat := {
  candidates := [
    { id := 1, preferences := [1, 2] },
    { id := 2, preferences := [1, 2] },
    { id := 3, preferences := [1, 2] },
    { id := 4, preferences := [1, 2] }
  ],
  posts := [
    { id := 1, capacity := 2, preferences := [1, 2, 3, 4] },
    { id := 2, capacity := 2, preferences := [4, 3, 2, 1] }
  ]
}



-- Pretty print matching
def printMatching (matching : Matching α β) : IO Unit := do
  for (c, p) in matching do
    IO.println s!"Candidate {c} assigned to Post {p}"

end GaleShapley101
