namespace Principia1687

/- Modern consequence used to make the historical comparison concrete. The
   historical Lemma X text will be added only after its Latin witness is
   archived and its geometric hypotheses are recorded. -/
theorem quadraticSagitta_modern
    (F m : ℝ) (hm : m ≠ 0) :
    ∃ c : ℝ, ∀ t : ℝ, (F / (2 * m)) * t ^ 2 = c * t ^ 2 :=
  ⟨F / (2 * m), fun _ => rfl⟩

end Principia1687
