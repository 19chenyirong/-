# 十六项验证条件

| 函数 | 验证条件 | 证明来源 | 结论 | 假设数 |
| --- | --- | --- | --- | --- |
| `LOS_ListInit` | `LOS_ListInit_return_wit_1` | 作者原有证明 | Qed | [3](assumptions/vc-LOS_ListInit_return_wit_1.out) |
| `LOS_ListAdd` | `LOS_ListAdd_return_wit_1` | 作者原有证明 | Qed | [3](assumptions/vc-LOS_ListAdd_return_wit_1.out) |
| `LOS_ListTailInsert` | `LOS_ListTailInsert_return_wit_1` | 作者原有证明 | Qed | [3](assumptions/vc-LOS_ListTailInsert_return_wit_1.out) |
| `LOS_ListTailInsert` | `LOS_ListTailInsert_partial_solve_wit_1` | 新增证明 | Qed | [2](assumptions/vc-LOS_ListTailInsert_partial_solve_wit_1.out) |
| `LOS_ListTailInsert` | `LOS_ListTailInsert_partial_solve_wit_2` | 新增证明 | Qed | [2](assumptions/vc-LOS_ListTailInsert_partial_solve_wit_2.out) |
| `LOS_ListTailInsert` | `LOS_ListTailInsert_which_implies_wit_1` | 作者原有证明 | Qed | [3](assumptions/vc-LOS_ListTailInsert_which_implies_wit_1.out) |
| `LOS_ListHeadInsert` | `LOS_ListHeadInsert_return_wit_1` | 新增证明 | Qed | [1](assumptions/vc-LOS_ListHeadInsert_return_wit_1.out) |
| `LOS_ListHeadInsert` | `LOS_ListHeadInsert_partial_solve_wit_1` | 新增证明 | Qed | [1](assumptions/vc-LOS_ListHeadInsert_partial_solve_wit_1.out) |
| `LOS_ListAdd` | `LOS_ListAdd_derive_high_level_spec_by_low_level_spec` | 作者原有证明 | Qed | [3](assumptions/vc-LOS_ListAdd_derive_high_level_spec_by_low_level_spec.out) |
| `LOS_ListDelete` | `LOS_ListDelete_safety_wit_1` | 新增证明 | Qed | [2](assumptions/vc-LOS_ListDelete_safety_wit_1.out) |
| `LOS_ListDelete` | `LOS_ListDelete_safety_wit_2` | 新增证明 | Qed | [2](assumptions/vc-LOS_ListDelete_safety_wit_2.out) |
| `LOS_ListDelete` | `LOS_ListDelete_return_wit_1` | 作者原有证明 | Qed | [3](assumptions/vc-LOS_ListDelete_return_wit_1.out) |
| `LOS_ListDelete` | `LOS_ListDelete_partial_solve_wit_1` | 新增证明 | Qed | [3](assumptions/vc-LOS_ListDelete_partial_solve_wit_1.out) |
| `LOS_ListDelete` | `LOS_ListDelete_partial_solve_wit_2` | 新增证明 | Qed | [3](assumptions/vc-LOS_ListDelete_partial_solve_wit_2.out) |
| `LOS_ListDelete` | `LOS_ListDelete_partial_solve_wit_3` | 新增证明 | Qed | [3](assumptions/vc-LOS_ListDelete_partial_solve_wit_3.out) |
| `LOS_ListDelete` | `LOS_ListDelete_derive_mid_level_spec_by_low_level_spec` | 作者原有证明 | Qed | [3](assumptions/vc-LOS_ListDelete_derive_mid_level_spec_by_low_level_spec.out) |
