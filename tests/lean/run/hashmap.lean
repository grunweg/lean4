import Std.Data.HashSet.Basic
import Std.Data.HashSet.Raw
import Std.Data.HashMap.AdditionalOperations

open Std

/-! Basic tests for (DHashMap|HashMap|HashSet)(.Raw)? functions which do not (yet) have proofs -/

namespace DHashMap.Raw

def m : DHashMap.Raw Nat (fun _ => Nat) :=
  .ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]

/-- info: [⟨2, 8⟩] -/
#guard_msgs in
#eval (m.filterMap fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [⟨3, none⟩, ⟨2, some 8⟩, ⟨1, none⟩] -/
#guard_msgs in
#eval (m.map fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [⟨3, 6⟩] -/
#guard_msgs in
#eval (m.filter fun _ v => v > 4).toList

def addValueToStateAndAddKey (acc : Nat) (k : Nat) (v : Nat) : StateM Nat Nat := do
  modify (fun st => st + v)
  return acc + k

/-- info: (18, 25) -/
#guard_msgs in
#eval (m.foldlM (init := 12) addValueToStateAndAddKey).run 13

/-- info: 18 -/
#guard_msgs in
#eval m.foldl (init := 12) fun acc k _ => acc + k

def addValueToState (_ : Nat) (v : Nat) : StateM Nat PUnit := do
  modify (fun st => st + v)

/-- info: ((), 25) -/
#guard_msgs in
#eval (m.forM addValueToState).run 13

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List (Nat × Nat) := []
  for ⟨k, v⟩ in m do
    ans := (k, v) :: ans
  return ans

/-- info: [⟨3, 6⟩, ⟨2, 4⟩, ⟨1, 2⟩] -/
#guard_msgs in
#eval m.toList

/-- info: #[⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval m.toArray

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval DHashMap.Raw.Const.toList m

/-- info: #[(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval DHashMap.Raw.Const.toArray m

/-- info: [3, 2, 1] -/
#guard_msgs in
#eval m.keys

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval m.keysArray

/-- info: [6, 4, 2] -/
#guard_msgs in
#eval m.values

/-- info: [⟨3, 6⟩, ⟨2, 4⟩, ⟨1, 2⟩, ⟨16, 9⟩] -/
#guard_msgs in
#eval (m.insertMany [⟨16, 8⟩, ⟨16, 9⟩]).toList

/-- info: [⟨3, 6⟩, ⟨2, 4⟩, ⟨1, 2⟩, ⟨16, 9⟩] -/
#guard_msgs in
#eval (DHashMap.Raw.Const.insertMany m [(16, 8), (16, 9)]).toList

/-- info: [⟨3, 6⟩, ⟨2, 4⟩, ⟨1, 2⟩] -/
#guard_msgs in
#eval (DHashMap.Raw.Const.ofList [(1, 2), (2, 4), (3, 6)]).toList

/-- info: Std.DHashMap.Raw.ofList [⟨1, 4⟩] -/
#guard_msgs in
#eval DHashMap.Raw.Const.ofList [(1, 2), (1, 4)]

end DHashMap.Raw

namespace DHashMap

def m : DHashMap Nat (fun _ => Nat) :=
  .ofList [⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩]

/-- info: [⟨2, 8⟩] -/
#guard_msgs in
#eval (m.filterMap fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [⟨3, none⟩, ⟨2, some 8⟩, ⟨1, none⟩] -/
#guard_msgs in
#eval (m.map fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [⟨3, 6⟩] -/
#guard_msgs in
#eval (m.filter fun _ v => v > 4).toList

def addValueToStateAndAddKey (acc : Nat) (k : Nat) (v : Nat) : StateM Nat Nat := do
  modify (fun st => st + v)
  return acc + k

/-- info: (18, 25) -/
#guard_msgs in
#eval (m.foldlM (init := 12) addValueToStateAndAddKey).run 13

/-- info: 18 -/
#guard_msgs in
#eval m.foldl (init := 12) fun acc k _ => acc + k

def addValueToState (_ : Nat) (v : Nat) : StateM Nat PUnit := do
  modify (fun st => st + v)

/-- info: ((), 25) -/
#guard_msgs in
#eval (m.forM addValueToState).run 13

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List (Nat × Nat) := []
  for ⟨k, v⟩ in m do
    ans := (k, v) :: ans
  return ans

/-- info: [⟨3, 6⟩, ⟨2, 4⟩, ⟨1, 2⟩] -/
#guard_msgs in
#eval m.toList

/-- info: #[⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 6⟩] -/
#guard_msgs in
#eval m.toArray

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval DHashMap.Const.toList m

/-- info: #[(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval DHashMap.Const.toArray m

/-- info: [3, 2, 1] -/
#guard_msgs in
#eval m.keys

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval m.keysArray

/-- info: [6, 4, 2] -/
#guard_msgs in
#eval m.values

/-- info: [⟨3, 6⟩, ⟨2, 4⟩, ⟨1, 2⟩, ⟨16, 9⟩] -/
#guard_msgs in
#eval (m.insertMany [⟨16, 8⟩, ⟨16, 9⟩]).toList

/-- info: [⟨3, 6⟩, ⟨2, 4⟩, ⟨1, 2⟩, ⟨16, 9⟩] -/
#guard_msgs in
#eval (DHashMap.Const.insertMany m [(16, 8), (16, 9)]).toList

/-- info: [⟨3, 6⟩, ⟨2, 4⟩, ⟨1, 2⟩] -/
#guard_msgs in
#eval (DHashMap.Const.ofList [(1, 2), (2, 4), (3, 6)]).toList

/-- info: Std.DHashMap.ofList [⟨1, 4⟩] -/
#guard_msgs in
#eval DHashMap.Const.ofList [(1, 2), (1, 4)]

end DHashMap

namespace HashMap.Raw

def m : HashMap.Raw Nat Nat :=
  .ofList [(1, 2), (2, 4), (3, 6)]

/-- info: [(2, 8)] -/
#guard_msgs in
#eval (m.filterMap fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [(3, none), (2, some 8), (1, none)] -/
#guard_msgs in
#eval (m.map fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [(3, 6)] -/
#guard_msgs in
#eval (m.filter fun _ v => v > 4).toList

def addValueToStateAndAddKey (acc : Nat) (k : Nat) (v : Nat) : StateM Nat Nat := do
  modify (fun st => st + v)
  return acc + k

/-- info: (18, 25) -/
#guard_msgs in
#eval (m.foldlM (init := 12) addValueToStateAndAddKey).run 13

/-- info: 18 -/
#guard_msgs in
#eval m.foldl (init := 12) fun acc k _ => acc + k

def addValueToState (_ : Nat) (v : Nat) : StateM Nat PUnit := do
  modify (fun st => st + v)

/-- info: ((), 25) -/
#guard_msgs in
#eval (m.forM addValueToState).run 13

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List (Nat × Nat) := []
  for (k, v) in m do
    ans := (k, v) :: ans
  return ans

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval m.toList

/-- info: #[(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval m.toArray

/-- info: [3, 2, 1] -/
#guard_msgs in
#eval m.keys

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval m.keysArray

/-- info: [6, 4, 2] -/
#guard_msgs in
#eval m.values

/-- info: [(3, 6), (2, 4), (1, 2), (16, 9)] -/
#guard_msgs in
#eval (m.insertMany [(16, 8), (16, 9)]).toList

/-- info: Std.HashMap.Raw.ofList [(1, 4)] -/
#guard_msgs in
#eval HashMap.Raw.ofList [(1, 2), (1, 4)]

end HashMap.Raw

namespace HashMap

def m : HashMap Nat Nat :=
  .ofList [(1, 2), (2, 4), (3, 6)]

/-- info: [(2, 8)] -/
#guard_msgs in
#eval (m.filterMap fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [(3, none), (2, some 8), (1, none)] -/
#guard_msgs in
#eval (m.map fun k v => if k % 2 == 0 then some (2 * v) else none).toList

/-- info: [(3, 6)] -/
#guard_msgs in
#eval (m.filter fun _ v => v > 4).toList

def addValueToStateAndAddKey (acc : Nat) (k : Nat) (v : Nat) : StateM Nat Nat := do
  modify (fun st => st + v)
  return acc + k

/-- info: (18, 25) -/
#guard_msgs in
#eval (m.foldlM (init := 12) addValueToStateAndAddKey).run 13

/-- info: 18 -/
#guard_msgs in
#eval m.foldl (init := 12) fun acc k _ => acc + k

def addValueToState (_ : Nat) (v : Nat) : StateM Nat PUnit := do
  modify (fun st => st + v)

/-- info: ((), 25) -/
#guard_msgs in
#eval (m.forM addValueToState).run 13

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List (Nat × Nat) := []
  for (k, v) in m do
    ans := (k, v) :: ans
  return ans

/-- info: [(3, 6), (2, 4), (1, 2)] -/
#guard_msgs in
#eval m.toList

/-- info: #[(1, 2), (2, 4), (3, 6)] -/
#guard_msgs in
#eval m.toArray

/-- info: [3, 2, 1] -/
#guard_msgs in
#eval m.keys

/-- info: #[1, 2, 3] -/
#guard_msgs in
#eval m.keysArray

/-- info: [6, 4, 2] -/
#guard_msgs in
#eval m.values

/-- info: [(3, 6), (2, 4), (1, 2), (16, 9)] -/
#guard_msgs in
#eval (m.insertMany [(16, 8), (16, 9)]).toList

/-- info: Std.HashMap.ofList [(1, 4)] -/
#guard_msgs in
#eval HashMap.ofList [(1, 2), (1, 4)]

end HashMap

namespace HashSet.Raw

def m : HashSet.Raw Nat :=
  .ofList [1, 2, 1000000000]

/-- info: [1000000000] -/
#guard_msgs in
#eval (m.filter fun v => v > 4).toList

def addKeyToStateAndAddKey (acc : Nat) (k : Nat) : StateM Nat Nat := do
  modify (fun st => st + k)
  return acc + k

/-- info: (1000000015, 1000000016) -/
#guard_msgs in
#eval (m.foldlM (init := 12) addKeyToStateAndAddKey).run 13

/-- info: 1000000015 -/
#guard_msgs in
#eval m.foldl (init := 12) fun acc k => acc + k

def addKeyToState (k : Nat) : StateM Nat PUnit := do
  modify (fun st => st + k)

/-- info: ((), 1000000016) -/
#guard_msgs in
#eval (m.forM addKeyToState).run 13

/-- info: [1000000000, 2, 1] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List Nat := []
  for k in m do
    ans := k :: ans
  return ans

/-- info: [1000000000, 2, 1] -/
#guard_msgs in
#eval m.toList

/-- info: #[1, 2, 1000000000] -/
#guard_msgs in
#eval m.toArray

/-- info: [1000000000, 2, 1, 16] -/
#guard_msgs in
#eval (m.insertMany [16, 16]).toList

/-- info: Std.HashSet.Raw.ofList [100, 1] -/
#guard_msgs in
#eval HashSet.Raw.ofList [1, 100]

end HashSet.Raw

namespace HashSet

def m : HashSet Nat :=
  .ofList [1, 2, 1000000000]

/-- info: [1000000000] -/
#guard_msgs in
#eval (m.filter fun v => v > 4).toList

def addKeyToStateAndAddKey (acc : Nat) (k : Nat) : StateM Nat Nat := do
  modify (fun st => st + k)
  return acc + k

/-- info: (1000000015, 1000000016) -/
#guard_msgs in
#eval (m.foldlM (init := 12) addKeyToStateAndAddKey).run 13

/-- info: 1000000015 -/
#guard_msgs in
#eval m.foldl (init := 12) fun acc k => acc + k

def addKeyToState (k : Nat) : StateM Nat PUnit := do
  modify (fun st => st + k)

/-- info: ((), 1000000016) -/
#guard_msgs in
#eval (m.forM addKeyToState).run 13

/-- info: [1000000000, 2, 1] -/
#guard_msgs in
#eval Id.run do
  let mut ans : List Nat := []
  for k in m do
    ans := k :: ans
  return ans

/-- info: [1000000000, 2, 1] -/
#guard_msgs in
#eval m.toList

/-- info: #[1, 2, 1000000000] -/
#guard_msgs in
#eval m.toArray

/-- info: [1000000000, 2, 1, 16] -/
#guard_msgs in
#eval (m.insertMany [16, 16]).toList

/-- info: Std.HashSet.ofList [100, 1] -/
#guard_msgs in
#eval HashSet.ofList [1, 100]

end HashSet
