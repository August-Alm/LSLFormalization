import Formalization.NormalForm

/-!
# Coherence from label disagreement

Two paths *clash* if, seen from the binder, they take different sides at the same position
of some fan label. A term is `Distinct` if the occurrences of each bound variable clash
pairwise. This implies `Coherent`, holds for `share t`, and is preserved by beta reduction;
neither fact needs local safety.
-/

namespace LSL

/-! ## Clashing paths -/

/-- The sides that `σ` has for label `l`, in order. -/
def fproj (l : Label) : Path → List Side
  | [] => []
  | (l', s) :: σ => if l' = l then s :: fproj l σ else fproj l σ

/-- The sides that the path `π` has for label `l`, nearest the binder first. -/
def bproj (l : Label) (π : Path) : List Side := fproj l π.reverse

/-- The lists differ at a position that both have. -/
def Diverge : List Side → List Side → Prop
  | a :: as, b :: bs => a ≠ b ∨ Diverge as bs
  | _, _ => False

def Clash (π ρ : Path) : Prop := ∃ l, Diverge (bproj l π) (bproj l ρ)

theorem fproj_append (l : Label) : ∀ (σ σ' : Path), fproj l (σ ++ σ') = fproj l σ ++ fproj l σ'
  | [], _ => rfl
  | (l', s) :: σ, σ' => by
    by_cases h : l' = l <;> simp [fproj, h, fproj_append l σ σ']

theorem bproj_append (l : Label) (π ρ : Path) : bproj l (π ++ ρ) = bproj l ρ ++ bproj l π := by
  simp [bproj, fproj_append]

theorem bproj_cons (l l' : Label) (s : Side) (π : Path) :
    bproj l ((l', s) :: π) = bproj l π ++ (if l' = l then [s] else []) := by
  simp only [bproj, List.reverse_cons, fproj_append, fproj]

theorem diverge_symm : ∀ (a b : List Side), Diverge a b → Diverge b a
  | [], _, h => by simp [Diverge] at h
  | _ :: _, [], h => by simp [Diverge] at h
  | a :: as, b :: bs, h => by
    simp only [Diverge] at h ⊢
    exact h.imp Ne.symm (diverge_symm as bs)

theorem diverge_append_left : ∀ (a b c : List Side), Diverge a b → Diverge (a ++ c) b
  | [], _, _, h => by simp [Diverge] at h
  | _ :: _, [], _, h => by simp [Diverge] at h
  | a :: as, b :: bs, c, h => by
    simp only [List.cons_append, Diverge] at h ⊢
    exact h.imp id (diverge_append_left as bs c)

theorem diverge_prefix : ∀ (c a b : List Side), Diverge a b → Diverge (c ++ a) (c ++ b)
  | [], _, _, h => h
  | x :: c, a, b, h => by
    simp only [List.cons_append, Diverge]
    exact .inr (diverge_prefix c a b h)

theorem diverge_ne : ∀ (a b x y : List Side), Diverge a b → a ++ x ≠ b ++ y
  | [], _, _, _, h => by simp [Diverge] at h
  | _ :: _, [], _, _, h => by simp [Diverge] at h
  | a :: as, b :: bs, x, y, h => by
    simp only [Diverge] at h
    intro heq
    simp only [List.cons_append, List.cons.injEq] at heq
    rcases h with h | h
    · exact h heq.1
    · exact diverge_ne as bs x y h heq.2

theorem Clash.symm {π ρ : Path} : Clash π ρ → Clash ρ π
  | ⟨l, h⟩ => ⟨l, diverge_symm _ _ h⟩

theorem Clash.append_left {ρ ρ' : Path} (π : Path) : Clash ρ ρ' → Clash (π ++ ρ) ρ'
  | ⟨l, h⟩ => ⟨l, by rw [bproj_append]; exact diverge_append_left _ _ _ h⟩

theorem Clash.append_right {ρ ρ' : Path} (π : Path) (h : Clash ρ ρ') : Clash ρ (π ++ ρ') :=
  (h.symm.append_left π).symm

theorem Clash.append_same {π π' : Path} (ρ : Path) : Clash π π' → Clash (π ++ ρ) (π' ++ ρ)
  | ⟨l, h⟩ => ⟨l, by rw [bproj_append, bproj_append]; exact diverge_prefix _ _ _ h⟩

/-! ## Clashing paths and the stacks -/

theorem pushPath_apply : ∀ (ρ : Path) (D : Stacks) (l : Label),
    pushPath D ρ l = bproj l ρ ++ D l
  | [], _, _ => rfl
  | (l', s) :: ρ, D, l => by
    simp only [pushPath]
    rw [pushPath_apply ρ (Stacks.push D l' s) l, bproj_cons, List.append_assoc]
    congr 1
    unfold Stacks.push
    by_cases h : l = l'
    · subst h
      simp
    · have h' : ¬ l' = l := fun e => h e.symm
      simp [h, h']

theorem popPath_some : ∀ (σ : Path) (S S' : Stacks), popPath S σ = some S' →
    ∀ l : Label, S l = fproj l σ ++ S' l
  | [], S, S', h, l => by
    simp only [popPath, Option.some.injEq] at h
    subst h
    rfl
  | (l', s) :: σ, S, S', h, l => by
    simp only [popPath] at h
    cases hS : S l' with
    | nil => simp [hS] at h
    | cons s' rest =>
      simp only [hS] at h
      by_cases hs : s' = s
      · subst hs
        simp only [ite_true] at h
        have ih := popPath_some σ _ S' h l
        by_cases hl : l' = l
        · subst hl
          simp only [ite_true] at ih
          simp only [fproj, ite_true, List.cons_append]
          rw [hS, ih]
        · have hl' : ¬ l = l' := fun e => hl e.symm
          simp only [hl', ite_false] at ih
          simp only [fproj, hl, ite_false]
          exact ih
      · simp [hs] at h

theorem popPath_append : ∀ (σ σ' : Path) (S : Stacks),
    popPath S (σ ++ σ') = (popPath S σ).bind (popPath · σ')
  | [], _, _ => rfl
  | (l, s) :: σ, σ', S => by
    simp only [List.cons_append, popPath]
    cases S l with
    | nil => rfl
    | cons s' rest =>
      by_cases hs : s' = s
      · simp only [hs, ite_true]
        exact popPath_append σ σ' _
      · simp [hs]

theorem popPath_pushPath : ∀ (π : Path) (D : Stacks), popPath (pushPath D π) π.reverse = some D
  | [], _ => rfl
  | (l, s) :: π, D => by
    rw [List.reverse_cons, popPath_append]
    simp only [pushPath]
    rw [popPath_pushPath π (Stacks.push D l s)]
    show popPath (Stacks.push D l s) [(l, s)] = some D
    simp only [popPath, Stacks.push, ite_true, Option.some.injEq]
    funext k
    by_cases h : k = l <;> simp [h]

theorem popPath_clash {π ρ : Path} (h : Clash π ρ) (D : Stacks) :
    popPath (pushPath D ρ) π.reverse = none := by
  obtain ⟨l, hl⟩ := h
  cases hp : popPath (pushPath D ρ) π.reverse with
  | none => rfl
  | some S' =>
    have h1 := popPath_some _ _ _ hp l
    rw [pushPath_apply] at h1
    exact absurd h1.symm (diverge_ne (bproj l π) (bproj l ρ) (S' l) (D l) hl)

theorem select_of_pairwise : ∀ (os : List (Addr × Path)) (o : Addr) (π : Path),
    (os.map Prod.snd).Pairwise Clash → (o, π) ∈ os →
      ∀ D : Stacks, select (pushPath D π) os = some (o, D)
  | [], _, _, _, hmem, _ => by simp at hmem
  | (o₁, π₁) :: rest, o, π, hp, hmem, D => by
    simp only [List.map_cons, List.pairwise_cons] at hp
    simp only [select, List.findSome?_cons]
    rcases List.mem_cons.mp hmem with heq | hrest
    · cases heq
      simp [popPath_pushPath]
    · have hc : Clash π₁ π := hp.1 π (List.mem_map.mpr ⟨(o, π), hrest, rfl⟩)
      simp only [popPath_clash hc D, Option.map_none]
      exact select_of_pairwise rest o π hp.2 hrest D

/-- No stacks have two clashing paths on top. -/
theorem popPath_unique {π ρ : Path} (h : Clash π ρ) {S S₁ S₂ : Stacks}
    (h₁ : popPath S π.reverse = some S₁) (h₂ : popPath S ρ.reverse = some S₂) : False := by
  obtain ⟨l, hl⟩ := h
  have e₁ := popPath_some _ _ _ h₁ l
  have e₂ := popPath_some _ _ _ h₂ l
  exact diverge_ne (bproj l π) (bproj l ρ) (S₁ l) (S₂ l) hl (e₁.symm.trans e₂)

theorem select_unique : ∀ (os : List (Addr × Path)) (o : Addr) (π : Path) (S S' : Stacks),
    (os.map Prod.snd).Pairwise Clash → (o, π) ∈ os → popPath S π.reverse = some S' →
      select S os = some (o, S')
  | [], _, _, _, _, _, hmem, _ => by simp at hmem
  | (o₁, π₁) :: rest, o, π, S, S', hp, hmem, hpop => by
    simp only [List.map_cons, List.pairwise_cons] at hp
    simp only [select, List.findSome?_cons]
    rcases List.mem_cons.mp hmem with heq | hrest
    · cases heq
      simp [hpop]
    · have hc : Clash π₁ π := hp.1 π (List.mem_map.mpr ⟨(o, π), hrest, rfl⟩)
      have hnone : popPath S π₁.reverse = none := by
        cases h₁ : popPath S π₁.reverse with
        | none => rfl
        | some S₁ => exact (popPath_unique hc h₁ hpop).elim
      simp only [hnone, Option.map_none]
      exact select_unique rest o π S S' hp.2 hrest hpop

theorem select_some : ∀ (os : List (Addr × Path)) (o : Addr) (S S' : Stacks),
    select S os = some (o, S') → ∃ π, (o, π) ∈ os ∧ popPath S π.reverse = some S'
  | [], _, _, _, h => by simp [select] at h
  | (o₁, π₁) :: rest, o, S, S', h => by
    simp only [select, List.findSome?_cons] at h
    cases h₁ : popPath S π₁.reverse with
    | none =>
      simp only [h₁, Option.map_none] at h
      obtain ⟨π, hm, hp⟩ := select_some rest o S S' h
      exact ⟨π, List.mem_cons_of_mem _ hm, hp⟩
    | some S₁ =>
      simp only [h₁, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨π₁, by simp, h₁⟩

/-- With pairwise clashing paths, `select` does not depend on the order of the occurrences. -/
theorem select_congr {os os' : List (Addr × Path)} (hp : (os'.map Prod.snd).Pairwise Clash)
    (hsub : ∀ x, x ∈ os → x ∈ os') {S : Stacks} {r : Addr × Stacks}
    (h : select S os = some r) : select S os' = some r := by
  obtain ⟨o, S'⟩ := r
  obtain ⟨π, hm, hpop⟩ := select_some os o S S' h
  exact select_unique os' o π S S' hp (hsub _ hm) hpop

/-! ## Distinct terms are coherent -/

/-- The paths of the occurrences of variable `i` in `t`, in order. -/
def paths : Nat → Term → List Path
  | i, .var k π => if k = i then [π] else []
  | i, .lam _ t => paths (i + 1) t
  | i, .app t u => paths i t ++ paths i u

/-- The occurrences of every bound variable have pairwise clashing paths. -/
def Distinct : Term → Prop
  | .var _ _ => True
  | .lam _ b => (paths 0 b).Pairwise Clash ∧ Distinct b
  | .app f u => Distinct f ∧ Distinct u

theorem occs_paths : ∀ (t : Term) (i : Nat) (a : Addr), (occs t i a).map Prod.snd = paths i t
  | .var j π, i, a => by
    simp only [occs, paths]
    split <;> rfl
  | .lam _ t, i, a => by
    simp only [occs, paths]
    exact occs_paths t (i + 1) _
  | .app f u, i, a => by
    simp only [occs, paths, List.map_append, occs_paths f, occs_paths u]

theorem distinct_sub {t : Term} (h : Distinct t) : ∀ (a : Addr) (s : Term),
    t.sub a = some s → Distinct s
  | [], s, hs => by
    simp only [Term.sub, List.foldr_nil, Option.some.injEq] at hs
    subst hs
    exact h
  | d :: a, s, hs => by
    rw [sub_cons] at hs
    cases hsa : t.sub a with
    | none => simp [hsa] at hs
    | some sa =>
      have hd := distinct_sub h a sa hsa
      rw [hsa] at hs
      cases sa with
      | var j ρ => cases d <;> simp [Term.child] at hs
      | lam A b =>
        cases d with
        | body =>
          simp only [Option.bind_some, Term.child, Option.some.injEq] at hs
          subst hs
          exact hd.2
        | fn => simp [Term.child] at hs
        | arg => simp [Term.child] at hs
      | app f u =>
        cases d with
        | body => simp [Term.child] at hs
        | fn =>
          simp only [Option.bind_some, Term.child, Option.some.injEq] at hs
          subst hs
          exact hd.1
        | arg =>
          simp only [Option.bind_some, Term.child, Option.some.injEq] at hs
          subst hs
          exact hd.2

theorem Distinct.coherent {t : Term} (h : Distinct t) : Coherent t := by
  intro b A body hb o π hmem D
  have hd := distinct_sub h b _ hb
  exact select_of_pairwise _ o π (by rw [occs_paths]; exact hd.1) hmem D

/-! ## Paths under shifting, grafting and substitution -/

theorem paths_shift_lt (d : Nat) : ∀ (s : Term) (i c : Nat), i < c →
    paths i (shift d c s) = paths i s
  | .var k π, i, c, h => by
    simp only [shift]
    split
    · rfl
    · have h1 : k + d ≠ i := by omega
      have h2 : k ≠ i := by omega
      simp [paths, h1, h2]
  | .lam _ b, i, c, h => by
    simp only [shift, paths]
    exact paths_shift_lt d b (i + 1) (c + 1) (by omega)
  | .app f u, i, c, h => by
    simp only [shift, paths, paths_shift_lt d f i c h, paths_shift_lt d u i c h]

theorem paths_shift_mid (d : Nat) : ∀ (s : Term) (i c : Nat), c ≤ i → i < c + d →
    paths i (shift d c s) = []
  | .var k π, i, c, h1, h2 => by
    simp only [shift]
    split
    · have h3 : k ≠ i := by omega
      simp [paths, h3]
    · have h3 : k + d ≠ i := by omega
      simp [paths, h3]
  | .lam _ b, i, c, h1, h2 => by
    simp only [shift, paths]
    exact paths_shift_mid d b (i + 1) (c + 1) (by omega) (by omega)
  | .app f u, i, c, h1, h2 => by
    simp only [shift, paths, paths_shift_mid d f i c h1 h2, paths_shift_mid d u i c h1 h2,
      List.append_nil]

theorem paths_shift_ge (d : Nat) : ∀ (s : Term) (i c : Nat), c + d ≤ i →
    paths i (shift d c s) = paths (i - d) s
  | .var k π, i, c, h => by
    simp only [shift]
    split
    · have h1 : k ≠ i := by omega
      have h2 : k ≠ i - d := by omega
      simp [paths, h1, h2]
    · by_cases h1 : k + d = i
      · have h2 : k = i - d := by omega
        simp [paths, h2]
        omega
      · have h2 : k ≠ i - d := by omega
        simp [paths, h1, h2]
  | .lam _ b, i, c, h => by
    simp only [shift, paths]
    rw [paths_shift_ge d b (i + 1) (c + 1) (by omega), show i + 1 - d = i - d + 1 by omega]
  | .app f u, i, c, h => by
    simp only [shift, paths, paths_shift_ge d f i c h, paths_shift_ge d u i c h]

theorem paths_graft_lt (π : Path) : ∀ (s : Term) (i c : Nat), i < c →
    paths i (graft π c s) = paths i s
  | .var k ρ, i, c, h => by
    simp only [graft]
    split
    · rfl
    · have h1 : k ≠ i := by omega
      simp [paths, h1]
  | .lam _ b, i, c, h => by
    simp only [graft, paths]
    exact paths_graft_lt π b (i + 1) (c + 1) (by omega)
  | .app f u, i, c, h => by
    simp only [graft, paths, paths_graft_lt π f i c h, paths_graft_lt π u i c h]

theorem paths_graft_ge (π : Path) : ∀ (s : Term) (i c : Nat), c ≤ i →
    paths i (graft π c s) = (paths i s).map (π ++ ·)
  | .var k ρ, i, c, h => by
    simp only [graft]
    split
    · have h1 : k ≠ i := by omega
      simp [paths, h1]
    · by_cases h1 : k = i <;> simp [paths, h1]
  | .lam _ b, i, c, h => by
    simp only [graft, paths]
    exact paths_graft_ge π b (i + 1) (c + 1) (by omega)
  | .app f u, i, c, h => by
    simp only [graft, paths, paths_graft_ge π f i c h, paths_graft_ge π u i c h, List.map_append]

theorem paths_graft_shift (π : Path) (s : Term) {i j : Nat} (h : j ≤ i) :
    paths i (graft π 0 (shift j 0 s)) = (paths (i - j) s).map (π ++ ·) := by
  rw [paths_graft_ge π _ i 0 (Nat.zero_le i), paths_shift_ge j s i 0 (by omega)]

theorem paths_subst_lt (s : Term) : ∀ (t : Term) (i j : Nat), i < j →
    paths i (subst j s t) = paths i t
  | .var k π, i, j, h => by
    simp only [subst]
    split
    · rfl
    · split
      · have h1 : k ≠ i := by omega
        rw [paths_graft_ge π _ i 0 (Nat.zero_le i), paths_shift_mid j s i 0 (Nat.zero_le i) (by omega)]
        simp [paths, h1]
      · have h1 : k ≠ i := by omega
        have h2 : k - 1 ≠ i := by omega
        simp [paths, h1, h2]
  | .lam _ b, i, j, h => by
    simp only [subst, paths]
    exact paths_subst_lt s b (i + 1) (j + 1) (by omega)
  | .app f u, i, j, h => by
    simp only [subst, paths, paths_subst_lt s f i j h, paths_subst_lt s u i j h]

/-- An occurrence in `subst j s t` comes from `t`, or from `s` at an occurrence of `j`. -/
theorem mem_paths_subst (s : Term) : ∀ (t : Term) (i j : Nat) (a : Path), j ≤ i →
    a ∈ paths i (subst j s t) →
      a ∈ paths (i + 1) t ∨ ∃ π ρ, π ∈ paths j t ∧ ρ ∈ paths (i - j) s ∧ a = π ++ ρ
  | .var k π, i, j, a, h, ha => by
    simp only [subst] at ha
    split at ha
    · have h1 : k ≠ i := by omega
      simp [paths, h1] at ha
    · split at ha
      · rename_i hkj
        rw [paths_graft_shift π s h] at ha
        obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp ha
        exact .inr ⟨π, ρ, by simp [paths, hkj], hρ, rfl⟩
      · by_cases h1 : k - 1 = i
        · have h2 : k = i + 1 := by omega
          simp only [paths, h1, ite_true, List.mem_singleton] at ha
          exact .inl (by simp [paths, h2, ha])
        · simp [paths, h1] at ha
  | .lam _ b, i, j, a, h, ha => by
    simp only [subst, paths] at ha
    rcases mem_paths_subst s b (i + 1) (j + 1) a (by omega) ha with h1 | ⟨π, ρ, hπ, hρ, rfl⟩
    · exact .inl h1
    · rw [Nat.add_sub_add_right] at hρ
      exact .inr ⟨π, ρ, hπ, hρ, rfl⟩
  | .app f u, i, j, a, h, ha => by
    simp only [subst, paths, List.mem_append] at ha ⊢
    rcases ha with ha | ha
    · rcases mem_paths_subst s f i j a h ha with h1 | ⟨π, ρ, hπ, hρ, rfl⟩
      · exact .inl (.inl h1)
      · exact .inr ⟨π, ρ, .inl hπ, hρ, rfl⟩
    · rcases mem_paths_subst s u i j a h ha with h1 | ⟨π, ρ, hπ, hρ, rfl⟩
      · exact .inl (.inr h1)
      · exact .inr ⟨π, ρ, .inr hπ, hρ, rfl⟩

theorem pairwise_of_ne {α : Type} {R : α → α → Prop} (hsymm : ∀ a b, R a b → R b a) :
    ∀ (l : List α), l.Pairwise R → ∀ a b, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: l, hp, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hne
      · rw [ha']
        exact hp.1 b hb'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb']
        exact hsymm _ _ (hp.1 a ha')
      · exact pairwise_of_ne hsymm l hp.2 a b ha' hb' hne

/-- The occurrences of an outer variable still clash pairwise after a substitution. -/
theorem pairwise_subst (s : Term) : ∀ (t : Term) (i j : Nat), j ≤ i →
    (paths j t).Pairwise Clash → (paths (i + 1) t).Pairwise Clash →
    (paths (i - j) s).Pairwise Clash →
    (∀ a, a ∈ paths (i + 1) t → ∀ b, b ∈ paths (i - j) s → Clash a b) →
      (paths i (subst j s t)).Pairwise Clash
  | .var k π, i, j, h, _, _, hs, _ => by
    simp only [subst]
    split
    · simp only [paths]
      split <;> simp
    · split
      · rw [paths_graft_shift π s h, List.pairwise_map]
        exact hs.imp fun hc => (hc.append_left π).append_right π
      · simp only [paths]
        split <;> simp
  | .lam _ b, i, j, h, hj, hi, hs, hcross => by
    simp only [subst, paths] at hj hi hcross ⊢
    refine pairwise_subst s b (i + 1) (j + 1) (by omega) hj hi ?_ ?_
    · rw [Nat.add_sub_add_right]
      exact hs
    · rw [Nat.add_sub_add_right]
      exact hcross
  | .app f u, i, j, h, hj, hi, hs, hcross => by
    simp only [subst, paths, List.pairwise_append, List.mem_append] at hj hi hcross ⊢
    refine ⟨pairwise_subst s f i j h hj.1 hi.1 hs fun a ha => hcross a (.inl ha),
      pairwise_subst s u i j h hj.2.1 hi.2.1 hs fun a ha => hcross a (.inr ha), ?_⟩
    intro a ha b hb
    rcases mem_paths_subst s f i j a h ha with ha1 | ⟨π, ρ, hπ, hρ, rfl⟩
    · rcases mem_paths_subst s u i j b h hb with hb1 | ⟨π', ρ', hπ', hρ', rfl⟩
      · exact hi.2.2 a ha1 b hb1
      · exact (hcross a (.inl ha1) ρ' hρ').append_right π'
    · rcases mem_paths_subst s u i j b h hb with hb1 | ⟨π', ρ', hπ', hρ', rfl⟩
      · exact ((hcross b (.inr hb1) ρ hρ).symm).append_left π
      · by_cases hρρ : ρ = ρ'
        · rw [← hρρ]
          exact (hj.2.2 π hπ π' hπ').append_same ρ
        · have hc := pairwise_of_ne (fun _ _ => Clash.symm) _ hs ρ ρ' hρ hρ' hρρ
          exact (hc.append_left π).append_right π'

theorem distinct_shift (d : Nat) : ∀ (s : Term) (c : Nat), Distinct s → Distinct (shift d c s)
  | .var k π, c, _ => by
    simp only [shift]
    split <;> trivial
  | .lam _ b, c, h => by
    simp only [shift]
    exact ⟨by rw [paths_shift_lt d b 0 (c + 1) (by omega)]; exact h.1, distinct_shift d b _ h.2⟩
  | .app f u, c, h => by
    simp only [shift]
    exact ⟨distinct_shift d f c h.1, distinct_shift d u c h.2⟩

theorem distinct_graft (π : Path) : ∀ (s : Term) (c : Nat), Distinct s → Distinct (graft π c s)
  | .var k ρ, c, _ => by
    simp only [graft]
    split <;> trivial
  | .lam _ b, c, h => by
    simp only [graft]
    exact ⟨by rw [paths_graft_lt π b 0 (c + 1) (by omega)]; exact h.1, distinct_graft π b _ h.2⟩
  | .app f u, c, h => by
    simp only [graft]
    exact ⟨distinct_graft π f c h.1, distinct_graft π u c h.2⟩

theorem distinct_subst {s : Term} (hs : Distinct s) : ∀ (t : Term) (j : Nat),
    Distinct t → Distinct (subst j s t)
  | .var k π, j, _ => by
    simp only [subst]
    split
    · trivial
    · split
      · exact distinct_graft π _ 0 (distinct_shift j s 0 hs)
      · trivial
  | .lam _ b, j, h => by
    simp only [subst]
    exact ⟨by rw [paths_subst_lt s b 0 (j + 1) (by omega)]; exact h.1, distinct_subst hs b _ h.2⟩
  | .app f u, j, h => by
    simp only [subst]
    exact ⟨distinct_subst hs f j h.1, distinct_subst hs u j h.2⟩

/-! ## Beta reduction keeps terms distinct -/

/-- A step keeps a term distinct, keeps the occurrences of each free variable clashing, and
only extends their paths at the occurrence end. -/
theorem step_paths {t t' : Term} (st : Step t t') :
    (Distinct t → Distinct t') ∧
    (Distinct t → ∀ i, (paths i t).Pairwise Clash → (paths i t').Pairwise Clash) ∧
    (∀ i ρ', ρ' ∈ paths i t' → ∃ π ρ, ρ ∈ paths i t ∧ ρ' = π ++ ρ) := by
  induction st with
  | @beta A b u =>
    refine ⟨fun h => distinct_subst h.2 b 0 h.1.2, fun h i hp => ?_, fun i ρ' hm => ?_⟩
    · simp only [paths, List.pairwise_append] at hp
      exact pairwise_subst u b i 0 (Nat.zero_le i) h.1.1 hp.1 hp.2.1 hp.2.2
    · rcases mem_paths_subst u b i 0 ρ' (Nat.zero_le i) hm with h1 | ⟨π, ρ, _, hρ, rfl⟩
      · exact ⟨[], ρ', by simp [paths, h1], rfl⟩
      · exact ⟨π, ρ, by simp only [paths, List.mem_append]; exact .inr hρ, rfl⟩
  | lam _ ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    exact ⟨fun h => ⟨ih2 h.2 0 h.1, ih1 h.2⟩, fun h i hp => ih2 h.2 (i + 1) hp,
      fun i ρ' hm => ih3 (i + 1) ρ' hm⟩
  | appL _ ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨fun h => ⟨ih1 h.1, h.2⟩, fun h i hp => ?_, fun i ρ' hm => ?_⟩
    · simp only [paths, List.pairwise_append] at hp ⊢
      refine ⟨ih2 h.1 i hp.1, hp.2.1, fun a ha b hb => ?_⟩
      obtain ⟨π, ρ, hρ, rfl⟩ := ih3 i a ha
      exact (hp.2.2 ρ hρ b hb).append_left π
    · simp only [paths, List.mem_append] at hm ⊢
      rcases hm with hm | hm
      · obtain ⟨π, ρ, hρ, rfl⟩ := ih3 i ρ' hm
        exact ⟨π, ρ, .inl hρ, rfl⟩
      · exact ⟨[], ρ', .inr hm, rfl⟩
  | appR _ ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨fun h => ⟨h.1, ih1 h.2⟩, fun h i hp => ?_, fun i ρ' hm => ?_⟩
    · simp only [paths, List.pairwise_append] at hp ⊢
      refine ⟨hp.1, ih2 h.2 i hp.2.1, fun a ha b hb => ?_⟩
      obtain ⟨π, ρ, hρ, rfl⟩ := ih3 i b hb
      exact (hp.2.2 a ha ρ hρ).append_right π
    · simp only [paths, List.mem_append] at hm ⊢
      rcases hm with hm | hm
      · exact ⟨[], ρ', .inl hm, rfl⟩
      · obtain ⟨π, ρ, hρ, rfl⟩ := ih3 i ρ' hm
        exact ⟨π, ρ, .inr hρ, rfl⟩

theorem Step.distinct {t t' : Term} (st : Step t t') (h : Distinct t) : Distinct t' :=
  (step_paths st).1 h

theorem Steps.distinct {t t' : Term} (st : Steps t t') : Distinct t → Distinct t' := by
  induction st with
  | refl => exact fun h => h
  | tail _ s ih => exact fun h => s.distinct (ih h)

/-! ## The initial sharing is distinct -/

/-- The fans that an occurrence passes on their `q` side. -/
def qs (base : Nat) : Nat → Path
  | 0 => []
  | m + 1 => (base + m, Side.q) :: qs base m

theorem qs_eq (base : Nat) : ∀ m : Nat,
    ((List.range m).reverse.map fun j => (base + j, Side.q)) = qs base m
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.reverse_append, List.map_append, qs_eq base m]
    rfl

theorem chain_eq (base n k : Nat) :
    chain base n k = (if k + 1 < n then [(base + k, Side.p)] else []) ++ qs base (min k (n - 1)) := by
  unfold chain
  rw [qs_eq]

theorem bproj_qs (base j : Nat) : ∀ m : Nat,
    bproj (base + j) (qs base m) = if j < m then [Side.q] else []
  | 0 => by simp [qs, bproj, fproj]
  | m + 1 => by
    rw [qs, bproj_cons, bproj_qs base j m]
    by_cases h1 : j < m
    · have h2 : ¬ m = j := by omega
      have h3 : j < m + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : j = m
      · subst h2
        simp
      · have h3 : ¬ m = j := by omega
        have h4 : ¬ j < m + 1 := by omega
        simp [h1, h3, h4]

theorem chain_clash {base n j k : Nat} (hjk : j < k) (hkn : k < n) :
    Clash (chain base n j) (chain base n k) := by
  refine ⟨base + j, ?_⟩
  have hj : bproj (base + j) (chain base n j) = [Side.p] := by
    rw [chain_eq, bproj_append, bproj_qs]
    have h1 : j + 1 < n := by omega
    have h2 : ¬ j < min j (n - 1) := by omega
    simp [h1, h2, bproj, fproj]
  have hk : bproj (base + j) (chain base n k) = [Side.q] := by
    rw [chain_eq, bproj_append, bproj_qs]
    have h2 : j < min k (n - 1) := by omega
    by_cases h1 : k + 1 < n
    · have h3 : ¬ k = j := by omega
      simp [h1, h2, h3, bproj, fproj]
    · simp [h1, h2, bproj, fproj]
  rw [hj, hk]
  simp [Diverge]

/-- The paths of occurrences `k, …, k + m - 1` of a variable with `n` occurrences. -/
def chains (base n : Nat) : Nat → Nat → List Path
  | _, 0 => []
  | k, m + 1 => chain base n k :: chains base n (k + 1) m

theorem chains_append (base n : Nat) : ∀ (m k m' : Nat),
    chains base n k m ++ chains base n (k + m) m' = chains base n k (m + m')
  | 0, k, m' => by simp [chains]
  | m + 1, k, m' => by
    have ih := chains_append base n m (k + 1) m'
    rw [show k + 1 + m = k + (m + 1) by omega] at ih
    rw [show m + 1 + m' = (m + m') + 1 by omega]
    simp only [chains, List.cons_append, ih]

theorem mem_chains (base n : Nat) : ∀ (m k : Nat) (a : Path), a ∈ chains base n k m →
    ∃ k', k ≤ k' ∧ k' < k + m ∧ a = chain base n k'
  | 0, _, _, h => by simp [chains] at h
  | m + 1, k, a, h => by
    simp only [chains, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨k, Nat.le_refl k, by omega, h⟩
    · obtain ⟨k', h1, h2, h3⟩ := mem_chains base n m (k + 1) a h
      exact ⟨k', by omega, by omega, h3⟩

theorem pairwise_chains (base n : Nat) : ∀ (m k : Nat), k + m ≤ n →
    (chains base n k m).Pairwise Clash
  | 0, _, _ => by simp [chains]
  | m + 1, k, h => by
    simp only [chains, List.pairwise_cons]
    refine ⟨fun b hb => ?_, pairwise_chains base n m (k + 1) (by omega)⟩
    obtain ⟨k', h1, h2, rfl⟩ := mem_chains base n m (k + 1) b hb
    exact chain_clash (by omega) (by omega)

theorem shareAux_lam (A : Ty) (b : Term) (env : List (Nat × Nat)) (seen : List Nat)
    (next : Nat) :
    shareAux (.lam A b) env seen next =
      (.lam A (shareAux b ((next, occurrences 0 b) :: env) (0 :: seen)
          (next + (occurrences 0 b - 1))).1,
        (shareAux b ((next, occurrences 0 b) :: env) (0 :: seen)
          (next + (occurrences 0 b - 1))).2.1.tail,
        (shareAux b ((next, occurrences 0 b) :: env) (0 :: seen)
          (next + (occurrences 0 b - 1))).2.2) := rfl

theorem shareAux_app (f u : Term) (env : List (Nat × Nat)) (seen : List Nat) (next : Nat) :
    shareAux (.app f u) env seen next =
      (.app (shareAux f env seen next).1
          (shareAux u env (shareAux f env seen next).2.1 (shareAux f env seen next).2.2).1,
        (shareAux u env (shareAux f env seen next).2.1 (shareAux f env seen next).2.2).2.1,
        (shareAux u env (shareAux f env seen next).2.1 (shareAux f env seen next).2.2).2.2) :=
  rfl

/-- `shareAux` gives the occurrences of a variable consecutive positions on its chain. -/
theorem shareAux_paths : ∀ (t : Term) (env : List (Nat × Nat)) (seen : List Nat) (next : Nat),
    env.length = seen.length →
      (shareAux t env seen next).2.1.length = seen.length ∧
      ∀ (i base n k : Nat), env[i]? = some (base, n) → seen[i]? = some k →
        (shareAux t env seen next).2.1[i]? = some (k + occurrences i t) ∧
        paths i (shareAux t env seen next).1 = chains base n k (occurrences i t)
  | .var j π, env, seen, next, hlen => by
    simp only [shareAux]
    split
    · rename_i bj nj kj hej hsj
      refine ⟨by simp, fun i base n k hi hk => ?_⟩
      by_cases hij : j = i
      · subst hij
        rw [hej] at hi
        rw [hsj] at hk
        cases hi
        cases hk
        have hlt : j < seen.length := by
          rcases Nat.lt_or_ge j seen.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hsj
            cases hsj
        simp [occurrences, paths, chains, hlt]
      · simp [occurrences, paths, chains, hij, List.getElem?_set_ne hij, hk]
    · rename_i hnone
      refine ⟨rfl, fun i base n k hi hk => ?_⟩
      have hij : j ≠ i := by
        intro e
        subst e
        exact hnone base n k hi hk
      simp [occurrences, paths, chains, hij, hk]
  | .lam A b, env, seen, next, hlen => by
    obtain ⟨ihlen, ih⟩ := shareAux_paths b ((next, occurrences 0 b) :: env) (0 :: seen)
      (next + (occurrences 0 b - 1)) (by simp [hlen])
    rw [shareAux_lam]
    refine ⟨by simp [ihlen], fun i base n k hi hk => ?_⟩
    obtain ⟨h1, h2⟩ := ih (i + 1) base n k (by simpa using hi) (by simpa using hk)
    exact ⟨by simpa [occurrences] using h1, by simpa [paths, occurrences] using h2⟩
  | .app f u, env, seen, next, hlen => by
    obtain ⟨hflen, hf⟩ := shareAux_paths f env seen next hlen
    obtain ⟨hulen, hu⟩ := shareAux_paths u env (shareAux f env seen next).2.1
      (shareAux f env seen next).2.2 (by rw [hflen]; exact hlen)
    rw [shareAux_app]
    refine ⟨hulen.trans hflen, fun i base n k hi hk => ?_⟩
    obtain ⟨f1, f2⟩ := hf i base n k hi hk
    obtain ⟨u1, u2⟩ := hu i base n (k + occurrences i f) hi f1
    refine ⟨by simpa [occurrences, Nat.add_assoc] using u1, ?_⟩
    simp only [paths, occurrences]
    rw [f2, u2, chains_append]

theorem distinct_shareAux : ∀ (t : Term) (env : List (Nat × Nat)) (seen : List Nat) (next : Nat),
    env.length = seen.length → Distinct (shareAux t env seen next).1
  | .var j π, env, seen, next, _ => by
    simp only [shareAux]
    split <;> trivial
  | .lam A b, env, seen, next, hlen => by
    have hlen' : ((next, occurrences 0 b) :: env).length = (0 :: seen).length := by simp [hlen]
    have hp := ((shareAux_paths b _ _ (next + (occurrences 0 b - 1)) hlen').2 0 next
      (occurrences 0 b) 0 rfl rfl).2
    rw [shareAux_lam]
    refine ⟨?_, distinct_shareAux b _ _ _ hlen'⟩
    rw [hp]
    exact pairwise_chains _ _ _ _ (by omega)
  | .app f u, env, seen, next, hlen => by
    rw [shareAux_app]
    exact ⟨distinct_shareAux f env seen next hlen,
      distinct_shareAux u env _ _ (by rw [(shareAux_paths f env seen next hlen).1]; exact hlen)⟩

theorem share_distinct (t : Term) : Distinct (share t) :=
  distinct_shareAux t [] [] 0 rfl

/-! ## Consequences -/

/-- Every term along the reduction of a term with its initial sharing is coherent. -/
theorem reduct_coherent {t₀ t : Term} (hs : Steps (share t₀) t) : Coherent t :=
  (hs.distinct (share_distinct t₀)).coherent

/-- A normal form reached from a locally safe term reads back as itself. -/
theorem reduct_readsBack {t₀ t : Term} {A : Ty} (hsafe : LocallySafe t₀ A)
    (hs : Steps (share t₀) t) (hnormal : ∀ t', ¬ Step t t') : ReadsBack t (erase t) :=
  normal_readsBack (reduct_safe hsafe hs) hnormal (reduct_coherent hs)

end LSL
