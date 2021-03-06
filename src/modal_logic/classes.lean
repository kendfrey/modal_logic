import tactic

namespace modal_logic

class modal_prop (α : Sort*) :=
  (not : α → α)
  (imp : α → α → α)
  (nec : α → α)
  
prefix `¬` := modal_prop.not
infixr ` ⇒ ` := modal_prop.imp
prefix `□`:90 := modal_prop.nec

def modal_prop.or {MProp} [modal_prop MProp] (p q : MProp) := ¬p ⇒ q
infixr ` ∨ ` := modal_prop.or

def modal_prop.and {MProp} [modal_prop MProp] (p q : MProp) := ¬(¬p ∨ ¬q)
infixr ` ∧ ` := modal_prop.and

def modal_prop.poss {MProp} [modal_prop MProp] (p : MProp) := ¬□¬p
prefix `◇`:90 := modal_prop.poss

def modal_prop.iff {MProp} [modal_prop MProp] (p q : MProp) := (p ⇒ q) ∧ (q ⇒ p)
infix ` ⇔ `:39 := modal_prop.iff

class has_sat (World : Type*) (MProp : Sort*) :=
  (sat : World → MProp → Prop)

infix ` ⊩ `:29 := has_sat.sat

class has_acc (World : Type*) :=
  (acc : World → World → Prop)

infix ` ≺ `:80 := has_acc.acc

class modal_logic (World MProp) [has_acc World] [modal_prop MProp] extends has_sat World MProp :=
  (sat_not (w : World) (p : MProp) : w ⊩ ¬p ↔ ¬(w ⊩ p))
  (sat_imp (w : World) (p q : MProp) : w ⊩ p ⇒ q ↔ w ⊩ p → w ⊩ q)
  (sat_nec (w : World) (p : MProp) : w ⊩ □p ↔ ∀ v, w ≺ v → v ⊩ p)

/--
`world` provides a definition of `World`.
An instance can be created to work with a specific type,
or it can be used as a parameter, when the type of `World` does not matter.
-/

class world :=
  (World : Type*)

def World [world] := world.World

/--
`modal_model` provides a complete modal model, with definitions for `MProp` and `≺`.
Typically an instance is created or imported to create the appropriate model for the situation.
-/

class modal_model extends world :=
  [has_acc : has_acc World]
  (MProp : Sort*)
  [modal_prop : modal_prop MProp]
  [modal_logic : modal_logic World MProp]

def MProp [modal_model] := modal_model.MProp

instance [modal_model] : modal_prop modal_model.MProp := modal_model.modal_prop
instance [modal_model] : modal_prop MProp := modal_model.modal_prop
instance [modal_model] : has_acc World := modal_model.has_acc
instance [modal_model] : modal_logic World MProp := modal_model.modal_logic

variables [modal_model : modal_model] (w : World) (p q : MProp)

lemma sat_not : w ⊩ ¬p ↔ ¬(w ⊩ p) := modal_logic.sat_not w p
lemma sat_imp : w ⊩ p ⇒ q ↔ w ⊩ p → w ⊩ q := modal_logic.sat_imp w p q
lemma sat_nec : w ⊩ □p ↔ ∀ v, w ≺ v → v ⊩ p := modal_logic.sat_nec w p

lemma sat_or : w ⊩ p ∨ q ↔ (w ⊩ p) ∨ (w ⊩ q) :=
  by simp only [modal_prop.or, sat_imp, sat_not, or_iff_not_imp_left]

lemma sat_and : w ⊩ p ∧ q ↔ (w ⊩ p) ∧ (w ⊩ q) :=
  by simp only [modal_prop.and, modal_prop.or, not_imp, not_not, sat_imp, sat_not]

lemma sat_poss : w ⊩ ◇p ↔ ∃ v, w ≺ v ∧ (v ⊩ p) :=
  by simp only [modal_prop.poss, exists_prop, sat_nec, sat_not, not_not, not_forall]

lemma sat_iff : w ⊩ p ⇔ q ↔ w ⊩ p ⇒ q ∧ q ⇒ p := iff.refl _

end modal_logic