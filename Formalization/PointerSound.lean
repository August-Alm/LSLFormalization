import Formalization.QNormal

/-!
# Soundness

A locally safe term with its initial sharing reads back as its normal form (`soundness`).

* The normal form reads back as itself with the pointer machine (`normal_qreads`).
* What a reduct reads back as with the pointer machine, the term reads back as
  (`qreads_steps`).
* On a locally safe term with distinct labels, every return of the pointer machine is to the
  newest exit to its lambda (`readbackLifo`), so the token machine makes the same steps
  (`follows`); hence readback with the pointer machine is readback with the token machine
  (`reads_of_qreads`).
-/

namespace LSL

/-- Unless a return is out of order, a run of the pointer machine without the history is a
run with it. -/
theorem prun_of_qeval {t : Term} : ∀ (k : Nat) (s : PState) (S : List Item),
    (∀ s', PReach t s s' → pstep t s' ≠ .parted) → qeval k t s.forget = some (some S) →
      ∃ s₁ H, PReach t s s₁ ∧ pstep t s₁ = .done S H ∧ prun k t s = some (S, H)
  | 0, _, _, _, h => by simp [qeval] at h
  | k + 1, s, S, hnp, h => by
    have hm := pstep_forget t s
    simp only [qeval] at h
    simp only [prun]
    cases hp : pstep t s with
    | next s' =>
      rw [hp] at hm
      cases hq : qstep t s.forget with
      | next s'' =>
        rw [hq] at hm h
        simp only [Matches] at hm
        subst hm
        obtain ⟨s₁, H, hr, hd, hrun⟩ :=
          prun_of_qeval k s' S (fun u hu => hnp u (.head hp hu)) h
        exact ⟨s₁, H, .head hp hr, hd, hrun⟩
      | done T =>
        rw [hq] at hm
        simp [Matches] at hm
      | stuck =>
        rw [hq] at hm
        simp [Matches] at hm
    | done T H =>
      rw [hp] at hm
      cases hq : qstep t s.forget with
      | next s'' =>
        rw [hq] at hm
        simp [Matches] at hm
      | done T' =>
        rw [hq] at hm h
        simp only [Matches] at hm
        subst hm
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨s, H, .refl, hp, rfl⟩
      | stuck =>
        rw [hq] at hm
        simp [Matches] at hm
    | stuck =>
      rw [hp] at hm
      cases hq : qstep t s.forget with
      | next s'' =>
        rw [hq] at hm
        simp [Matches] at hm
      | done T' =>
        rw [hq] at hm
        simp [Matches] at hm
      | stuck =>
        rw [hq] at h
        simp at h
    | parted => exact absurd hp (hnp s .refl)

/-- Where the pointer machine stops with an empty tape, the token machine is stuck. -/
theorem stuck_of_starved {t : Term} (hd : Distinct t) (ha : Apart t) (S₀ : Stacks) :
    ∀ (k : Nat) (s : PState) (s₁ : QState), (∀ s', PReach t s s' → pstep t s' ≠ .parted) →
      qiter t k s.forget = some s₁ → Starved t s₁ → ∀ n, run n t (s.abs t S₀) = none
  | 0, s, s₁, _, hk, hst, n => by
    simp only [qiter, Option.some.injEq] at hk
    subst hk
    apply not_out_of_stuck
    obtain ⟨pos, tape, log, hist⟩ := s
    change Starved t ⟨pos, tape, log⟩ at hst
    cases hst with
    | lam hs => exact step_lam_nil hs _
    | fn => simp [PState.abs, step]
  | k + 1, s, s₁, hnp, hk, hst, n => by
    have hm := pstep_forget t s
    have hf := follows hd ha S₀ s
    simp only [qiter] at hk
    cases hq : qstep t s.forget with
    | next s'' =>
      rw [hq] at hk hm
      cases hp : pstep t s with
      | next s' =>
        rw [hp] at hm hf
        simp only [Matches] at hm
        subst hm
        simp only [Follows] at hf
        cases n with
        | zero => rfl
        | succ n =>
          simp only [run, hf]
          exact stuck_of_starved hd ha S₀ k s' s₁ (fun u hu => hnp u (.head hp hu)) hk hst n
      | done T H =>
        rw [hp] at hm
        simp [Matches] at hm
      | stuck =>
        rw [hp] at hm
        simp [Matches] at hm
      | parted => exact absurd hp (hnp s .refl)
    | done T =>
      rw [hq] at hk
      simp at hk
    | stuck =>
      rw [hq] at hk
      simp at hk

theorem abs_start (t : Term) (U : List Item) (j : Nat) (H : List Addr) :
    PState.abs t Stacks.empty ⟨.down [], U ++ List.replicate j .q, [], H⟩ =
      ⟨.down [], stacksOf t Stacks.empty H, U.map Item.side ++ List.replicate j .q⟩ := by
  simp [PState.abs, Item.side]

/-- On a locally safe term with distinct labels, readback with the pointer machine is
readback with the token machine. -/
theorem reads_of_qreads {t : Term} {A : Ty} (hsafe : LocallySafe t A) (hd : Distinct t)
    (ha : Apart t) {anc : List Frame} {U : List Item} {u : Tm} (hq : QReads t anc U u) :
    ∀ H : List Addr, Point t U H →
      Reads t anc (stacksOf t Stacks.empty H) (U.map Item.side) u := by
  induction hq with
  | @node anc U V n l m x e B args hout hmin hV hres hvt har hlen _ ih =>
    intro H hp
    have hnp : ∀ (j : Nat) (s' : PState),
        PReach t ⟨.down [], U ++ List.replicate j .q, [], H⟩ s' → pstep t s' ≠ .parted :=
      fun j s' hr => readbackLifo t A hsafe U H hp j s' hr
    obtain ⟨k, hk⟩ := hout
    obtain ⟨s₁, H', hr, hdone, hrun⟩ :=
      prun_of_qeval k ⟨.down [], U ++ List.replicate n .q, [], H⟩ _ (hnp n) hk
    have htok := run_of_prun hd ha Stacks.empty k _ _ _ hrun
    rw [abs_start] at htok
    have hS : (V ++ List.replicate l Item.q ++ Item.p e :: List.replicate m Item.q).map
        Item.side = V.map Item.side ++ List.replicate l .q ++ .p :: List.replicate m .q := by
      simp [Item.side]
    rw [hS] at htok
    refine Reads.node (sem_root.mpr ⟨k, htok⟩) (fun j hj => ?_) (parse_addr hV) hres hlen
      (fun i a hi => ?_)
    · rintro ⟨out, hsem⟩
      obtain ⟨n', hn'⟩ := sem_root.mp hsem
      obtain ⟨k', s₂, hk', hst⟩ := hmin j hj
      have hno := stuck_of_starved hd ha Stacks.empty k'
        ⟨.down [], U ++ List.replicate j Item.q, [], H⟩ s₂ (hnp j) hk' hst n'
      rw [abs_start] at hno
      rw [hno] at hn'
      cases hn'
    · obtain ⟨pre, post, hsp, hpl⟩ := getElem?_split args i a hi
      have hi' : i < args.length := by
        rw [hsp, ← hpl]
        simp only [List.length_append, List.length_cons]
        omega
      have hpt : Point t (childTape V l e i) H' := Point.arg hp hr hdone hvt (by omega)
      have h := ih i a hi H' hpt
      rw [childTape_sides] at h
      exact h

/-- Soundness: a locally safe term with its initial sharing reads back as the normal form of
any of its reductions. -/
theorem soundness {t₀ v : Term} {A : Ty} (hsafe : LocallySafe t₀ A) (hs : Steps (share t₀) v)
    (hn : ∀ v', ¬ Step v v') : ReadsBack (share t₀) (erase v) :=
  reads_of_qreads (share_safe hsafe) (share_distinct t₀) (share_apart t₀)
    (qreads_steps hs (normal_qreads (reduct_safe hsafe hs) hn)) [] .root

end LSL
