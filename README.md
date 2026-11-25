# Applied Purist Vol. I — Lean 4 Formal Verification (`PuristSiliconCore`)

Mathlib-free Lean 4.36.0 / Lake 5.0 formal verification suite (**155 `KERNEL_ONLY` theorems, `0 sorry`, `0 native_decide`**)
+ C99 silicon baseline (`c_silicon/solinas_ct.c`) for **Applied Purist Vol. I (Quantitative Finance Core)** ([`10.5281/zenodo.24104901`](https://doi.org/10.5281/zenodo.24104901) | Companion SW [`10.5281/zenodo.24133639`](https://doi.org/10.5281/zenodo.24133639)) & `https://lean.bhutadamarasena.com/`.

## Reproduce
    lake build && lake exe purist_audit ./proof-manifest.json

## Coverage & Scope Boundaries
- **Formally Proved in Lean (`155/155 KERNEL_ONLY`, `0 sorry`):**
  - **Volterra Complexity & Weighted KYP Passivity (`Vol1RoughVolCore`):** Exact O(N^2) convolution sum N*(N+1), weighted 8-mode Stieltjes KYP passivity M_KYP(P) < 0 with P = diag(R_1..R_8) (`||PB - C^T||_inf = 0` & strict negative definiteness), and Table 2.1 eigenvalue bound (`2*p_1*R_1 > 6.99e-6`).
  - **4D Kustaanheimo-Stiefel Spinor Algebra (`Vol1RoughVolCore`):** Non-negativity `V(u) = ||u||^2 >= 0`, exact orthogonality `L(u)^T L(u) = ||u||^2 I_4`, Euler 4-square norm `||L(u)v||^2 = ||u||^2 ||v||^2`, physical lift `||L(u)u||^2 = ||u||^4`, bilinear gauge symmetry `l(u,v)=0 => L(u)v = L(v)u`, and Kunita pullback contraction bracket (`0.995488 < 1`).
  - **Arbitrary-N Filtering, Givens & Bitwise LOB (`Vol1RoughVolCore`, `D106AndBitwise`):** General N-dimensional Bierman-Thornton `UDU^T` strict positive definiteness, 2x2 Givens SRIF norm preservation, and 64-level bitwise LOB `popcnt`/`rotl_64` conservation.
  - **Payoff Smoothing, EFT & 64-Byte WebGPU ABI (`MarketState64Abi`, `AlgebraicPhysicsAndEft`, `SolinasPocklington`):** European call 1-Lipschitz convexity, Lasry-Lions `L = 5.5556` & `0.2250` bounds, `MarketState64` 16-lane alignment & `asset_id` (+12 B) immutability, Knuth/Dekker D106 EFT identities, and Pocklington primality (`p64_is_prime`, `p106_is_prime`).
- **Outside Mathlib-Free Scope (Not Claimed as Lean-Proved):** Complex Pick-Nevanlinna contour integral (`Thm 2.1`), continuous Chebyshev minimax bound, continuous Ito calculus derivations (`Thm 4.1`/`4.2`), Hilbert-space Lasry-Lions Frechet differentiability (`Thm 6.1`), continuous KMB quantum density metric, and empirical M3 Max / RTX 4090 GPU timings (120.0 FPS, 0.82 ms).
- **OPSEC Boundary:** Proprietary web UI, WASM/WebGPU applets, `TMD-Hash v11.0/v12.0` internals, and NUMS scripts excluded (`TMD12-BB` black-box only).

## Citation
    @article{unmani2026puristvol1,
      author  = {Ghulam-e-Shah-e-Unmani, Arya Arunachala Ananda},
      title   = {{Non-Markovian Rough Volatility in O(1) Step Complexity: Minimal Stinespring-KYP Operator Dilations, Kustaanheimo-Stiefel Feller-Boundary Regularization, and Microsecond WebGPU Execution}},
      journal = {Applied Purist Series},
      volume  = {I},
      year    = {2026},
      doi     = {10.5281/zenodo.24104901}
    }

    @software{unmani2026puristvol1lean,
      author    = {Ghulam-e-Shah-e-Unmani, Arya Arunachala Ananda},
      title     = {{Applied Purist Series Vol. I — Lean 4 Formal Verification & Silicon ABI Archive}},
      version   = {1.0.0},
      year      = {2026},
      publisher = {Zenodo},
      license   = {CC-BY-4.0},
      url       = {https://lean.bhutadamarasena.com/}
    }
# Applied-Purist-Vol1-Lean-Verification
