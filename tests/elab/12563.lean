/-!
  # Make `linter.all` option also control `linter.unusedSectionVars`, `linter.omit` and `linter.loopingSimpArgs`
-/

/-!
  ## `linter.unusedSectionVars`
-/

namespace UnusedSectionVars

section

set_option linter.unusedSectionVars true

variable {α : Type} [ToString α]

/--
warning: automatically included section variable(s) unused in theorem `UnusedSectionVars.myTheorem1`:
  [ToString α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ToString α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
-/
#guard_msgs in
theorem myTheorem1 (a : α) : a = a := rfl

end

section

set_option linter.all true

variable {α : Type} [ToString α]

/--
warning: automatically included section variable(s) unused in theorem `UnusedSectionVars.myTheorem2`:
  [ToString α]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ToString α] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
-/
#guard_msgs in
theorem myTheorem2 (a : α) : a = a := rfl

end

section

set_option linter.all false

variable {α : Type} [ToString α]

theorem myTheorem3 (a : α) : a = a := rfl

end

end UnusedSectionVars

/-!
  ## `linter.omit`
-/

namespace Omit

section

set_option linter.omit true

variable (α : Type)

/--
warning: `omit` should be avoided in favor of restructuring your `variable` declarations

Note: This linter can be disabled with `set_option linter.omit false`
-/
#guard_msgs in
omit α

end

section

set_option linter.all true

variable (α : Type)

/--
warning: `omit` should be avoided in favor of restructuring your `variable` declarations

Note: This linter can be disabled with `set_option linter.omit false`
-/
#guard_msgs in
omit α

end

section

set_option linter.all false

variable (α : Type)

omit α

end

end Omit

/-!
  ## `linter.loopingSimpArgs`
-/

namespace LoopingSimpArgs

axiom testSorry : α

opaque a : Nat
opaque b : Nat

theorem ab : a = b := testSorry
theorem ba : b = a := testSorry
theorem aa : a = id a := testSorry

section

set_option linter.loopingSimpArgs true
set_option maxRecDepth 20

/--
warning: Possibly looping simp theorem: `aa`

Note: Possibly caused by: `id`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : id a = 23 := by simp -failIfUnchanged only [aa, id]

end

section

set_option linter.all true
set_option maxRecDepth 20

/--
warning: Possibly looping simp theorem: `aa`

Note: Possibly caused by: `id`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : id a = 23 := by simp -failIfUnchanged only [aa, id]

end

-- TODO: Add test showing that `set_option linter.all false` makes a difference.

end LoopingSimpArgs
