import tactic

namespace modal_logic

class has_acc (World : Type*) :=
  (acc : World → World → Prop)

infix ` ≺ `:80 := has_acc.acc

/--
`world` provides a definition of `World` and `MProp`.
An instance can be created to work with a specific type,
or it can be used as a parameter, when the type of `World` does not matter.
-/

class world :=
  (World : Type*)

def World [world] := world.World
def MProp [world] := World → Prop

/--
`modal_frame` provides a definition of `≺`.
-/

class modal_frame extends world, has_acc World

variables [_modal_frame : modal_frame] (w : World) (p q : MProp)

def sat : Prop := p w
infix ` ⊩ `:29 := sat
def not : MProp := λ w, ¬(w ⊩ p)
prefix `¬` := not
def imp : MProp := λ w, w ⊩ p → w ⊩ q
infixr ` ⇒ ` := imp
def iff : MProp := λ w, w ⊩ p ↔ w ⊩ q
infixr ` ⇔ `:39 := iff
def and : MProp := λ w, (w ⊩ p) ∧ (w ⊩ q)
infixr ` ∧ ` := and
def or : MProp := λ w, (w ⊩ p) ∨ (w ⊩ q)
infixr ` ∨ ` := or
def nec : MProp := λ w, ∀ v, w ≺ v → v ⊩ p
prefix `□`:90 := nec
def poss : MProp := λ w, ∃ v, w ≺ v ∧ (v ⊩ p)
prefix `◇`:90 := poss

@[ext] lemma mpropext [modal_frame] {p q : MProp} : (∀ w : World, w ⊩ p ⇔ q) → p = q :=
begin
  intros h,
  ext w,
  apply h,
end

end modal_logic