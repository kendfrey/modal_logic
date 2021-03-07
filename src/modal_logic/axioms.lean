import modal_logic.tactic

universes u

class is_dense (α : Type u) (r : α → α → Prop) : Prop :=
(dense : ∀ a b, r a b → ∃ c, r a c ∧ r c b)

instance is_refl.is_dense {α r} [is_refl α r] : is_dense α r := ⟨λ a b h, ⟨a, refl a, h⟩⟩

class is_serial (α : Type u) (r : α → α → Prop) : Prop :=
(serial : ∀ a, ∃ b, r a b)

instance is_refl.is_serial {α r} [is_refl α r] : is_serial α r := ⟨λ a, ⟨a, refl a⟩⟩

class is_euclidean (α : Type u) (r : α → α → Prop) : Prop :=
(euc : ∀ a b c, r a b → r a c → r b c)

instance is_per.is_euclidean {α r} [is_per α r] : is_euclidean α r := ⟨λ a b c h h', trans (symm h) h'⟩

class is_semieuclidean (α : Type u) (r : α → α → Prop) :=
(semieuc : ∀ a b c, r a b → r a c → r b c ∨ r c b)

instance is_euclidean.is_semieuclidean {α r} [is_euclidean α r] : is_semieuclidean α r := ⟨λ a b c h h', or.inl (is_euclidean.euc a b c h h')⟩

class is_founded (α : Type u) (r : α → α → Prop) : Prop :=
(founded : ∀ a, ∃ b, r a b ∧ ∀ c, r b c → b = c)

class is_convergent (α : Type u) (r : α → α → Prop) : Prop :=
(conv : ∀ a b c, r a b → r a c → ∃ d, r b d ∧ r c d)

class is_discrete (α : Type u) (r : α → α → Prop) : Prop :=
(disc : ∀ a b, r a b → a = b)

class is_functional (α : Type u) (r : α → α → Prop) : Prop :=
(func : ∀ a b c, r a b → r a c → b = c)

class is_function (α : Type u) (r : α → α → Prop) extends is_serial α r, is_functional α r : Prop

instance is_discrete.is_functional {α r} [is_discrete α r] : is_functional α r := ⟨λ a b c h h', eq.trans (is_discrete.disc a b h).symm (is_discrete.disc a c h')⟩

class is_right_refl (α : Type u) (r : α → α → Prop) : Prop :=
(refl : ∀ a b, r a b → r b b)

instance is_refl.is_right_refl {α r} [is_refl α r] : is_right_refl α r := ⟨λ a b h, refl b⟩

namespace modal_logic

open modal_logic

variables [modal_model : modal_model] (w : World) (p q : MProp)

lemma em : w ⊩ p ∨ ¬p :=
  by simp only [modal_prop.or, sat_imp, imp_self]

lemma dne : w ⊩ ¬¬p ⇒ p :=
  by simp only [sat_imp, sat_not, not_not, imp_self]

lemma or_of_not_imp : w ⊩ (¬p ⇒ q) ⇒ (p ∨ q) :=
begin
  simp only [modal_prop.or],
  m.intros h,
  m.apply h,
end

lemma nec_imp_nec_of_nec_imp : w ⊩ □(p ⇒ q) ⇒ □p ⇒ □q :=
begin
  m.intros h h' v h_v,
  m.apply h,
  {
    apply h_v,
  },
  {
    m.apply h',
    apply h_v,
  },
end

lemma of_nec [is_refl World (≺)] : w ⊩ □p ⇒ p :=
begin
  m.intros h,
  m.apply h,
  m.apply refl,
end

lemma nec_nec_of_nec [is_trans World (≺)] : w ⊩ □p ⇒ □□p :=
begin
  m.intros h v h_v u h_u,
  m.apply h,
  apply trans h_v h_u,
end

lemma nec_of_nec_nec [is_dense World (≺)] : w ⊩ □□p ⇒ □p :=
begin
  m.intros h v h_v,
  rcases is_dense.dense w v h_v with ⟨u, h_u, h_u'⟩,
  m.apply h _ h_u _ h_u',
end

lemma poss_of_nec [is_serial World (≺)] : w ⊩ □p ⇒ ◇p :=
begin
  m.intros h,
  rcases @is_serial.serial World (≺) _ w with ⟨v, h_v⟩,
  m.use [v, h_v],
  m.apply h,
  apply h_v,
end

lemma nec_poss [is_symm World (≺)] : w ⊩ p ⇒ □◇p :=
begin
  m.intros h v h_v,
  m.use [w, symm h_v],
  m.apply h,
end

lemma nec_poss_of_poss [is_euclidean World (≺)] : w ⊩ ◇p ⇒ □◇p :=
begin
  m.intros h v h_v,
  m.cases h with u h_u h',
  m.use [u, is_euclidean.euc w v u h_v h_u],
  m.apply h',
end

lemma nec_of_nec_nec_imp [is_trans World (≺)] (wf : well_founded (λ w v : World, v ≺ w)) : w ⊩ □(□p ⇒ p) ⇒ □p :=
begin
  apply well_founded.induction wf w,
  m.intros v ih h u h_u,
  m.apply h _ h_u,
  m.apply ih u h_u,
  m.intros t h_t,
  m.apply h,
  apply trans h_u h_t,
end

lemma of_nec_nec_imp_nec_imp [is_preorder World (≺)] (wf : well_founded (λ w v : World, w ≠ v ∧ v ≺ w)) : w ⊩ □(□(p ⇒ □p) ⇒ p) ⇒ p :=
begin
  have : is_antisymm World (≺),
  {
    constructor,
    intros v u h_u h_v,
    have := well_founded.has_min wf {v, u} ⟨v, set.mem_insert _ _⟩,
    rcases this with ⟨t, h_t, h⟩,
    simp only [set.mem_insert_iff, set.mem_singleton_iff, not_and, not_imp_not] at h h_t,
    rcases h_t with rfl | rfl,
    {
      symmetry,
      apply h u _ h_u,
      right,
      refl,
    },
    {
      apply h v _ h_v,
      left,
      refl,
    },
  },
  m.intros h,
  m.apply dne,
  m.intros h_w_p,
  have : ∃ v, w ≺ v ∧ ¬(v ⊩ p) ∧ ∀ u, u ≠ v → v ≺ u → u ⊩ p,
  {
    rcases well_founded.has_min wf { v | w ≺ v ∧ ¬(v ⊩ p) } ⟨w, refl w, h_w_p⟩ with ⟨v, ⟨h_v, h_v'⟩, h'⟩,
    simp only [set.mem_set_of_eq, and_imp, not_imp_not] at h',
    use [v, h_v, h_v'],
    intros u h_u h_u',
    apply h' u (trans h_v h_u') h_u h_u',
  },
  rcases this with ⟨v, h_v, h_v_p, h'⟩,
  apply h_v_p,
  m.apply h v h_v,
  m.intros u h_u h_u_p,
  have h'' : u ≠ v,
  {
    rintros rfl,
    contradiction,
  },
  m.intros t h_t,
  by_cases h''' : t = u,
  {
    subst t,
    apply h_u_p,
  },
  {
    have h'''' : t ≠ v,
    {
      rintros rfl,
      apply h'',
      exactI antisymm h_t h_u,
    },
    apply h' t h'''',
    apply trans h_u h_t,
  },
end

lemma nec_nec_imp_or_nec_nec_imp [is_semieuclidean World (≺)] : w ⊩ □(□p ⇒ q) ∨ □(□q ⇒ p) :=
begin
  m.apply or_of_not_imp,
  m.intros h v h_v h',
  m.apply dne,
  m.intro h'',
  m.apply h,
  m.intros u h_u h''',
  cases is_semieuclidean.semieuc w v u h_v h_u with h_u' h_v',
  {
    m.apply h' _ h_u',
  },
  {
    exfalso,
    m.apply h'',
    m.apply h''' _ h_v',
  },
end

lemma poss_nec_of_nec_poss [is_trans World (≺)] [is_founded World (≺)] : w ⊩ □◇p ⇒ ◇□p :=
begin
  m.intros h,
  rcases @is_founded.founded World (≺) _ w with ⟨v, h_v, h_v'⟩,
  m.use [v, h_v],
  m.intros u h_u,
  m.cases h v h_v with t h_t h',
  rw ← h_v' u h_u,
  rw h_v' t h_t,
  m.apply h',
end

lemma nec_poss_of_poss_nec [is_convergent World (≺)] : w ⊩ ◇□p ⇒ □◇p :=
begin
  m.intros h v h_v,
  m.cases h with u h_u h',
  rcases is_convergent.conv w v u h_v h_u with ⟨t, h_t, h_t'⟩,
  m.use [t, h_t],
  m.apply h' t h_t',
end

lemma nec_of [is_discrete World (≺)] : w ⊩ p ⇒ □p :=
begin
  m.intros h u h_u,
  rw ← is_discrete.disc w u h_u,
  m.apply h,
end

lemma nec_of_poss [is_functional World (≺)] : w ⊩ ◇p ⇒ □p :=
begin
  m.intros h v h_v,
  m.cases h with u h_u h',
  rw is_functional.func w v u h_v h_u,
  m.apply h',
end

lemma nec_iff_poss [is_function World (≺)] : w ⊩ ◇p ⇔ □p :=
begin
  m.split,
  {
    m.apply nec_of_poss,
  },
  {
    m.apply poss_of_nec,
  },
end

lemma nec_nec_imp [is_right_refl World (≺)] : w ⊩ □(□p ⇒ p) :=
begin
  m.intros v h_v h,
  m.apply h,
  apply is_right_refl.refl w v h_v,
end

end modal_logic