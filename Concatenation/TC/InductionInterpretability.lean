module

public import Concatenation.TC.ISigma
public import Concatenation.TC.TallyArithmetic

/-!
# $\Sigma_n\text{-}\mathsf{TCI}$ and $\mathsf{I}\Sigma_n$ are mutually interpretable

$\mathsf{I}\Sigma_n$ interprets $\Sigma_n\text{-}\mathsf{TCI}$ by the bijective binary numerals,
and $\Sigma_{n+1}\text{-}\mathsf{TCI}$ interprets $\mathsf{I}\Sigma_{n+1}$ by the tallies. For
$n = 0$, $\Sigma_0\text{-}\mathsf{TCI}$ interprets $\mathsf{I}\Sigma_0$ through $\mathsf{Q}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
$\Sigma_n\text{-}\mathsf{TCI}$ and $\mathsf{I}\Sigma_n$ are mutually interpretable.
- [HH14, Question 3]
-/
theorem TCISigma_mutuallyInterpretable_ISigma : ∀ n : ℕ, Nonempty (TCISigma n ⋈ 𝗜𝚺 n)
  | 0 => ⟨⟨TCISigma.interpretationISigma0, binaryInterpretation 0⟩⟩
  | n + 1 => ⟨⟨tallyInterpretation n, binaryInterpretation (n + 1)⟩⟩

end FFL.FirstOrder.Concatenation
