import modal_logic.classes
import init.meta.interactive

open modal_logic
open tactic
open lean.parser
open interactive
open interactive.types

namespace tactic.interactive

meta def m.intro (h : parse ident_) : tactic unit := do
  t ← target,
  match t with
  | `(%%w ⊩ modal_prop.imp %%p %%q) := `[refine (sat_imp %%w %%p %%q).mpr _]
  | `(%%w ⊩ modal_prop.nec %%p) := `[refine (sat_nec %%w %%p).mpr _]
  | `(%%w ⊩ modal_prop.not %%p) := `[refine (sat_not %%w %%p).mpr _]
  | _ := skip
  end,
  intro h

meta def m.intros (hs : parse (many ident_)) : tactic unit := hs.mmap' m.intro

add_hint_tactic "m.intros _"

meta def m.apply : parse texpr → tactic unit := λ h,
  `[refine %%h] <|>
  do
    t ← i_to_expr_no_subgoals h >>= infer_type,
    match t with
    | `(%%w ⊩ modal_prop.imp %%p %%q) := m.apply ``((sat_imp %%w %%p %%q).mp %%h _)
    | `(%%w ⊩ modal_prop.nec %%p) := m.apply ``((sat_nec %%w %%p).mp %%h _ _)
    | `(%%w ⊩ modal_prop.not %%p) := m.apply ``((sat_not %%w %%p).mp %%h _)
    | (expr.pi x bi d h') := m.apply ``(%%h _)
    | _ := `[apply %%h] -- This fails with a decent enough error message
    end

-- This is a hack to get `cases` to unpack `∃ x, P x ∧ Q x` in a single step.
inductive exists_triple (α : Sort*) (p : α → Prop) (q : α → Prop) : Prop
| intro (x : α) : p x → q x → exists_triple

lemma sat_poss_triple [modal_model] (w : World) (p : MProp) : w ⊩ ◇p → exists_triple World (λ v, w ≺ v) (λ v, v ⊩ p) :=
begin
  rw sat_poss,
  rintros ⟨v, h_v, h⟩,
  exact ⟨v, h_v, h⟩,
end

meta def m.cases (h : parse texpr) (hs : parse with_ident_list) : tactic unit := do
  t ← i_to_expr h >>= infer_type,
  let h := match t with
  | `(%%w ⊩ modal_prop.and %%p %%q) := ``((sat_and %%w %%p %%q).mp %%h)
  | `(%%w ⊩ modal_prop.or %%p %%q) := ``((sat_or %%w %%p %%q).mp %%h)
  | `(%%w ⊩ modal_prop.iff %%p %%q) := ``((sat_and %%w (%%p ⇒ %%q) (%%q ⇒ %%p)).mp %%h)
  | `(%%w ⊩ modal_prop.poss %%p) := ``(sat_poss_triple %%w %%p %%h)
  | _ := h
  end,
  cases (none, h) hs

meta def m.use (_ : parse (tk "[")) (w : parse texpr) (_ : parse (tk ",")) (h : parse texpr) (_ : parse (tk "]")) : tactic unit := do
  t ← target,
  match t with
  | `(%%v ⊩ modal_prop.poss %%p) := `[refine (sat_poss %%v %%p).mpr ⟨%%w, %%h, _⟩]
  | _ := fail "m.use failed, goal is not a possibility statement"
  end

meta def m.split : tactic unit := do
  t ← target,
  match t with
  | `(%%w ⊩ modal_prop.and %%p %%q) := `[refine ((sat_and %%w %%p %%q).mpr _), split]
  | `(%%w ⊩ modal_prop.iff %%p %%q) := `[refine ((sat_and %%w (%%p ⇒ %%q) (%%q ⇒ %%p)).mpr _), split]
  | _ := split
  end

add_hint_tactic "m.split"

meta def m.left : tactic unit := do
  t ← target,
  match t with
  | `(%%w ⊩ modal_prop.or %%p %%q) := `[refine ((sat_or %%w %%p %%q).mpr _), left]
  | _ := left
  end

add_hint_tactic "m.left"

meta def m.right : tactic unit := do
  t ← target,
  match t with
  | `(%%w ⊩ modal_prop.or %%p %%q) := `[refine ((sat_or %%w %%p %%q).mpr _), right]
  | _ := right
  end

add_hint_tactic "m.right"

section test

variables [modal_model : modal_model] (w : World) (p q r : MProp)

-- tests intros with imp
example : w ⊩ p ⇒ p :=
begin
  hint,
  m.intros h,
  m.apply h,
end

-- tests intros with nec
example : w ⊩ □(p ⇒ p) :=
begin
  hint,
  m.intros v h_v h,
  m.apply h,
end

-- tests intros with not
example : w ⊩ ¬¬(p ⇒ p) :=
begin
  hint,
  m.intros h,
  m.apply h,
  m.intros h',
  m.apply h',
end

-- tests apply with imp
example : w ⊩ (p ⇒ q ⇒ r) ⇒ p ⇒ q ⇒ r :=
begin
  m.intros h h' h'',
  m.apply h,
  {
    m.apply h',
  },
  {
    m.apply h'',
  },
end

-- tests apply with nec
example : w ⊩ □p ⇒ □p :=
begin
  m.intros h v h_v,
  m.apply h,
  m.apply h_v,
end

-- tests apply with not
example : w ⊩ ¬p ⇒ ¬p :=
begin
  m.intros h h',
  m.apply h,
  m.apply h',
end

-- tests cases with and
example : w ⊩ (p ∧ q) ⇒ p :=
begin
  m.intros h,
  m.cases h with h' h'',
  m.apply h',
end

-- tests cases with or
example : w ⊩ (p ∨ q) ⇒ ¬p ⇒ q :=
begin
  m.intros h,
  m.cases h with h' h',
  {
    m.intros h'',
    exfalso,
    m.apply h'',
    m.apply h',
  },
  {
    m.intros h'',
    m.apply h',
  },
end

-- tests cases with iff
example : w ⊩ (p ⇔ q) ⇒ p ⇒ q :=
begin
  m.intros h,
  m.cases h with h' h'',
  m.apply h',
end

-- tests cases with poss
-- tests use
example : w ⊩ □(p ⇒ q) ⇒ ◇p ⇒ ◇q :=
begin
  m.intros h h',
  m.cases h' with v h_v h'',
  m.use [v, h_v],
  m.apply h,
  {
    m.apply h_v,
  },
  {
    m.apply h'',
  },
end

-- tests split with and
example : w ⊩ p ⇒ q ⇒ (p ∧ q) :=
begin
  m.intros h h',
  hint,
  m.split,
  {
    m.apply h,
  },
  {
    m.apply h',
  },
end

-- tests split with iff
example : w ⊩ p ⇒ q ⇒ (p ⇔ q) :=
begin
  m.intros h h',
  hint,
  m.split,
  {
    m.intros h'',
    m.apply h',
  },
  {
    m.intros h'',
    m.apply h,
  },
end

-- tests left
example : w ⊩ p ⇒ (p ∨ q) :=
begin
  m.intros h,
  hint,
  m.left,
  m.apply h,
end

-- tests right
example : w ⊩ q ⇒ (p ∨ q) :=
begin
  m.intros h,
  hint,
  m.right,
  m.apply h,
end

end test

end tactic.interactive