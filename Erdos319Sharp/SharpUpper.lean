import Erdos319Sharp.OmissionNormalization
import Erdos319Sharp.Reduction

set_option autoImplicit false

open Filter Finset Erdos319Formal
open scoped Topology

noncomputable section

namespace Erdos319Sharp

theorem sharpUpperWitnesses_proved : SharpUpperWitnesses := by
  intro ε hε
  have hBound := tendsto_constructionOmissionNormalized.eventually
    (Iio_mem_nhds (by linarith : Real.exp (-Real.eulerMascheroniConstant) <
      Real.exp (-Real.eulerMascheroniConstant) + ε))
  filter_upwards [eventually_primitive_construction, hBound, eventually_positive_scale]
    with N hConstruct hBoundN hScale
  obtain ⟨A, hA, hPrimitive, hOmission⟩ := hConstruct
  refine ⟨A, hA, hPrimitive, lt_of_le_of_lt ?_ hBoundN⟩
  unfold normalizedOmissions constructionOmissionNormalized
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hOmission hScale.2.1.le) (mul_pos hScale.1 hScale.2.2).le

end Erdos319Sharp
