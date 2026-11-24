import Formalization.SubstAddr

/-!
# The pointer machine under a beta step: the moves around the redex

For the redex `(λ M) N` at `r` of `t`, the machine on `t` needs extra steps where the
machine on the reduct needs none:

* to get from the redex to `M` and back (`enter_body`, `leave_body`);
* to get from an occurrence of the variable to `N` and back (`enter_copy`, `leave_copy`).
  On the way in, the exit from the occurrence becomes the log entry for `N` (`withArg`).

`Loc` says which address of `t` an address of the reduct stands for. The simulation of the
other steps is in `BetaStep.lean`.
-/

namespace LSL

/-- `k` steps of the machine. -/
def qiter (t : Term) : Nat → QState → Option QState
  | 0, s => some s
  | k + 1, s =>
    match qstep t s with
    | .next s' => qiter t k s'
    | _ => none

theorem qiter_add (t : Term) : ∀ (j k : Nat) (s s₁ s₂ : QState), qiter t j s = some s₁ →
    qiter t k s₁ = some s₂ → qiter t (j + k) s = some s₂
  | 0, k, s, s₁, s₂, h₁, h₂ => by
    simp only [qiter, Option.some.injEq] at h₁
    subst h₁
    simpa using h₂
  | j + 1, k, s, s₁, s₂, h₁, h₂ => by
    rw [show j + 1 + k = (j + k) + 1 by omega]
    simp only [qiter] at h₁ ⊢
    cases hs : qstep t s with
    | next s' =>
      simp only [hs] at h₁ ⊢
      exact qiter_add t j k s' s₁ s₂ h₁ h₂
    | done T => simp [hs] at h₁
    | stuck => simp [hs] at h₁

/-- The log of a place in the copy of `N` at the occurrence `e` of the variable, below `k`
arguments of `N`, made from the log `L` of the place in the reduct: the entry for `N` is the
exit from the occurrence, with the entries for the arguments of `M` around it saved. -/
def withArg (r : Addr) (k : Nat) (e : Addr) (L : List Exit) : List Exit :=
  L.take k ++ .mk (e ++ .body :: .fn :: r) ((L.drop k).take (argDepth e)) ::
    L.drop (k + argDepth e)

theorem withArg_zero (r e : Addr) (L : List Exit) : withArg r 0 e L =
    .mk (e ++ .body :: .fn :: r) (L.take (argDepth e)) :: L.drop (argDepth e) := by
  simp [withArg]

theorem withArg_cons (r : Addr) (k : Nat) (e : Addr) (x : Exit) (L : List Exit) :
    withArg r (k + 1) e (x :: L) = x :: withArg r k e L := by
  simp [withArg, Nat.add_right_comm k 1 (argDepth e)]

section

variable {t : Term} {r : Addr} {A : Ty} {M N : Term} {t' : Term}

theorem Redex.sub_fn (h : Redex t r A M N t') : t.sub (.fn :: r) = some (.lam A M) := by
  rw [sub_cons, h.sub]
  rfl

/-- The lambda of the redex binds the occurrences of the variable. -/
theorem Redex.binder_occ (e : Addr) :
    binder (e ++ .body :: .fn :: r) (bodies e) = .inr (.fn :: r) := by
  rw [binder_append, binder_ge e _ (Nat.le_refl _)]
  simp [binder]

theorem Redex.binderOf_occ (h : Redex t r A M N t') {e : Addr} {π : Path}
    (hs : M.sub e = some (.var (bodies e) π)) :
    binderOf t (e ++ .body :: .fn :: r) = some (.fn :: r) := by
  simp [binderOf, h.sub_body, hs, Redex.binder_occ]

/-- From the redex to `M`. -/
theorem enter_body (h : Redex t r A M N t') (T : List Item) (L : List Exit) :
    qiter t 2 ⟨.down r, T, L⟩ = some ⟨.down (.body :: .fn :: r), T, L⟩ := by
  simp [qiter, qstep, h.sub, h.sub_fn]

/-- From `M` back to the redex. -/
theorem leave_body (t : Term) (r : Addr) (T : List Item) (L : List Exit) :
    qiter t 2 ⟨.up (.body :: .fn :: r), T, L⟩ = some ⟨.up r, T, L⟩ := by
  simp [qiter, qstep]

/-- From an occurrence of the variable to `N`. -/
theorem enter_copy (h : Redex t r A M N t') {e : Addr} {π : Path}
    (hs : M.sub e = some (.var (bodies e) π)) (T : List Item) (L : List Exit) :
    qiter t 2 ⟨.down (e ++ .body :: .fn :: r), T, L⟩ =
      some ⟨.down (.arg :: r), T, withArg r 0 e L⟩ := by
  have hd : argDepth (e ++ .body :: .fn :: r) - argDepth r = argDepth e := by
    simp [argDepth_append]
  simp [qiter, qstep, h.sub_body, hs, Redex.binder_occ, hd, withArg_zero]

/-- From `N` back to the occurrence of the variable. -/
theorem leave_copy (h : Redex t r A M N t') {e : Addr} {π : Path}
    (hs : M.sub e = some (.var (bodies e) π)) (T : List Item) (L : List Exit) :
    qiter t 2 ⟨.up (.arg :: r), T, withArg r 0 e L⟩ =
      some ⟨.up (e ++ .body :: .fn :: r), T, L⟩ := by
  simp [qiter, qstep, withArg_zero, h.sub_fn, h.binderOf_occ hs, Exit.occ, Exit.saved]

/-- `Loc a' a ins`: the address `a'` of the reduct stands for the address `a` of `t`. It lies
outside the redex, in `M`, or in the copy of `N` at an occurrence `e` of the variable; in the
last case `ins` is `e` with the number of arguments of `N` around the place. -/
inductive Loc (t : Term) (r : Addr) (M N : Term) : Addr → Addr → Option (Nat × Addr) → Prop
  | out {a : Addr} {s : Term} : ¬ r <:+ a → t.sub a = some s → Loc t r M N a a none
  | body {e : Addr} {s : Term} : M.sub e = some s → s.kind ≠ .var (bodies e) →
      Loc t r M N (e ++ r) (e ++ .body :: .fn :: r) none
  | copy {e : Addr} {π : Path} {n : Addr} {s : Term} : M.sub e = some (.var (bodies e) π) →
      N.sub n = some s → Loc t r M N (n ++ e ++ r) (n ++ .arg :: r) (some (argDepth n, e))

/-- `ins` for the child in direction `d`. -/
def insChild (ins : Option (Nat × Addr)) (d : Dir) : Option (Nat × Addr) :=
  ins.map fun (k, e) => (if d = .arg then k + 1 else k, e)

/-- The log at a place of `t`, for the log at the place of the reduct that it stands for.
`R` relates the logs entry by entry. -/
def LogSim (R : List Exit → List Exit → Prop) (r : Addr) :
    Option (Nat × Addr) → List Exit → List Exit → Prop
  | none, L', L => R L' L
  | some (k, e), L', L => ∃ L₀, R L' L₀ ∧ L = withArg r k e L₀

theorem sub_parent {t : Term} {d : Dir} {e : Addr} {s : Term} (h : t.sub (d :: e) = some s) :
    ∃ s₀, t.sub e = some s₀ ∧ ∀ i, s₀.kind ≠ .var i := by
  rw [sub_cons] at h
  cases h₀ : t.sub e with
  | none => simp [h₀] at h
  | some s₀ =>
    refine ⟨s₀, rfl, fun i hk => ?_⟩
    rw [h₀] at h
    cases s₀ with
    | var j π => cases d <;> simp [Term.child] at h
    | lam _ _ => simp [Term.kind] at hk
    | app _ _ => simp [Term.kind] at hk

theorem kind_var {s : Term} {i : Nat} (h : s.kind = .var i) : ∃ π, s = .var i π := by
  cases s with
  | var j π =>
    simp only [Term.kind, Kind.var.injEq] at h
    subst h
    exact ⟨π, rfl⟩
  | lam _ _ => simp [Term.kind] at h
  | app _ _ => simp [Term.kind] at h

theorem argDepth_cons (d : Dir) (n : Addr) :
    argDepth (d :: n) = if d = .arg then argDepth n + 1 else argDepth n := by
  cases d <;> simp

/-- After a step down to the child in direction `d`, the machine on `t` gets to the place
that the child in the reduct stands for. -/
theorem arrive (h : Redex t r A M N t') {R : List Exit → List Exit → Prop} {a' a : Addr}
    {ins : Option (Nat × Addr)} (hloc : Loc t r M N a' a ins) (d : Dir) {c : Term}
    (hc : t.sub (d :: a) = some c) (T : List Item) {L' L : List Exit}
    (hlog : LogSim R r (insChild ins d) L' L) :
    ∃ k a₂ ins₂ L₂, qiter t k ⟨.down (d :: a), T, L⟩ = some ⟨.down a₂, T, L₂⟩ ∧
      Loc t r M N (d :: a') a₂ ins₂ ∧ LogSim R r ins₂ L' L₂ := by
  cases hloc with
  | out hr hv =>
    by_cases hr' : r <:+ d :: a'
    · have hreq : r = d :: a' := (List.suffix_cons_iff.mp hr').resolve_right hr
      subst hreq
      have h2 := enter_body h T L
      by_cases hk : M.kind = .var 0
      · obtain ⟨π, rfl⟩ := kind_var hk
        have hs : (Term.var 0 π).sub [] = some (.var (bodies []) π) := rfl
        have h3 := enter_copy h hs T L
        exact ⟨4, _, _, _, qiter_add t 2 2 _ _ _ h2 h3, Loc.copy (n := []) hs rfl, ⟨L, hlog, rfl⟩⟩
      · exact ⟨2, _, _, _, h2, Loc.body (e := []) rfl (by simpa using hk), hlog⟩
    · exact ⟨0, _, _, _, rfl, Loc.out hr' hc, hlog⟩
  | @body e s hs hk =>
    have hc' : M.sub (d :: e) = some c := (h.sub_body (d :: e)).symm.trans hc
    by_cases hk' : c.kind = .var (bodies (d :: e))
    · obtain ⟨π, rfl⟩ := kind_var hk'
      have h3 := enter_copy h hc' T L
      exact ⟨2, _, _, _, h3, Loc.copy (n := []) hc' rfl, ⟨L, hlog, rfl⟩⟩
    · exact ⟨0, _, _, _, rfl, Loc.body hc' hk', hlog⟩
  | @copy e π n s hs hn =>
    have hc' : N.sub (d :: n) = some c := (h.sub_arg (d :: n)).symm.trans hc
    refine ⟨0, _, _, _, rfl, Loc.copy hs hc', ?_⟩
    change ∃ L₀, R L' L₀ ∧ L = withArg r (if d = .arg then argDepth n + 1 else argDepth n) e L₀
      at hlog
    obtain ⟨L₀, hR, rfl⟩ := hlog
    exact ⟨L₀, hR, by rw [argDepth_cons]⟩

/-- Before a step up, the machine on `t` gets from the place that a place in the reduct
stands for to the child of the place that the parent stands for. -/
theorem depart (h : Redex t r A M N t') {R : List Exit → List Exit → Prop} {a' a : Addr}
    {ins : Option (Nat × Addr)} (hloc : Loc t r M N a' a ins) (T : List Item) {L' L : List Exit}
    (hlog : LogSim R r ins L' L) :
    ∃ k a₁ L₁, qiter t k ⟨.up a, T, L⟩ = some ⟨.up a₁, T, L₁⟩ ∧ (a' = [] → a₁ = []) ∧
      ∀ d p', a' = d :: p' → ∃ p insp, a₁ = d :: p ∧ Loc t r M N p' p insp ∧
        LogSim R r (insChild insp d) L' L₁ := by
  cases hloc with
  | out hr hv =>
    refine ⟨0, _, L, rfl, id, fun d p' hp => ?_⟩
    subst hp
    obtain ⟨s₀, hs₀, _⟩ := sub_parent hv
    exact ⟨p', none, rfl, Loc.out (fun hs => hr (hs.trans (List.suffix_cons d p'))) hs₀, hlog⟩
  | @body e s hs hk =>
    cases e with
    | nil =>
      refine ⟨2, r, L, leave_body t r T L, fun h0 => h0, fun d p' hp => ?_⟩
      have hp' : r = d :: p' := hp
      have hsub := h.sub
      rw [hp'] at hsub
      obtain ⟨s₀, hs₀, _⟩ := sub_parent hsub
      refine ⟨p', none, hp', Loc.out (fun hsuf => ?_) hs₀, hlog⟩
      have hlen := hsuf.length_le
      rw [hp', List.length_cons] at hlen
      omega
    | cons d₀ e₀ =>
      obtain ⟨s₀, hs₀, hk₀⟩ := sub_parent hs
      refine ⟨0, _, L, rfl, fun h0 => by simp at h0, fun d p' hp => ?_⟩
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨e₀ ++ .body :: .fn :: r, none, rfl, Loc.body hs₀ (hk₀ _), hlog⟩
  | @copy e π n s hs hn =>
    change ∃ L₀, R L' L₀ ∧ L = withArg r (argDepth n) e L₀ at hlog
    obtain ⟨L₀, hR, rfl⟩ := hlog
    cases n with
    | cons d₀ n₀ =>
      obtain ⟨s₀, hs₀, _⟩ := sub_parent hn
      refine ⟨0, _, _, rfl, fun h0 => by simp at h0, fun d p' hp => ?_⟩
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨n₀ ++ .arg :: r, some (argDepth n₀, e), rfl, Loc.copy hs hs₀, ?_⟩
      show ∃ L₁, R L' L₁ ∧ withArg r (argDepth (d₀ :: n₀)) e L₀ =
        withArg r (if d₀ = .arg then argDepth n₀ + 1 else argDepth n₀) e L₁
      exact ⟨L₀, hR, by rw [argDepth_cons]⟩
    | nil =>
      have h1 := leave_copy h hs T L₀
      cases e with
      | nil =>
        have h2 := leave_body t r T L₀
        refine ⟨4, r, L₀, qiter_add t 2 2 _ _ _ h1 h2, fun h0 => h0, fun d p' hp => ?_⟩
        have hp' : r = d :: p' := hp
        have hsub := h.sub
        rw [hp'] at hsub
        obtain ⟨s₁, hs₁, _⟩ := sub_parent hsub
        refine ⟨p', none, hp', Loc.out (fun hsuf => ?_) hs₁, hR⟩
        have hlen := hsuf.length_le
        rw [hp', List.length_cons] at hlen
        omega
      | cons d₀ e₀ =>
        obtain ⟨s₀, hs₀, hk₀⟩ := sub_parent hs
        refine ⟨2, _, L₀, h1, fun h0 => by simp at h0, fun d p' hp => ?_⟩
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨e₀ ++ .body :: .fn :: r, none, rfl, Loc.body hs₀ (hk₀ _), hR⟩

end

end LSL
