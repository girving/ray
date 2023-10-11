import Std.Tactic.LabelAttr

/-!
## `bound_rules` label for use with the `bound` tactic
-/

open Lean Elab Meta

-- Rules used by the bound tactic
register_label_attr bound_rules

-- Trace class for the bound tactic
initialize registerTraceClass `bound
