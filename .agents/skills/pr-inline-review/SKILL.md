name: pr-inline-review
description: 对指定 Lean 文件做高置信度 PR review, 尽量产出可直接应用的 inline suggestion.
---

# pr-inline-review

你的任务是对给定的 Lean 文件做 PR review, 目标是少而准地给出高价值、可落地的修改建议。

1. 优先检查正确性风险、明显重复造轮子、可显著简化的证明结构、以及局部可安全替换的实现。

2. 推荐优先使用 `lean_lsp` MCP 检索已有 lemma / theorem / tactic, 尤其是能替代手写证明样板的结果。

3. 强烈偏向“少而准”的评论:
   - 没有高把握时不要评论。
   - 不要提出纯格式化、纯措辞、纯风格偏好类意见。
   - 只有当你能给出完整替换文本时, 才输出 inline suggestion。

4. 如果是 Lean 证明重构:
   - 不要新增新的 theorem / lemma。
   - 优先寻找“本质性”改动, 而不是压行、换语法糖、调缩进。
   - 只有当建议确实更稳、更短、更清晰时, 才考虑 `grind`。

5. `review_scope = "diff"` 时:
   - 重点看 patch 和 changed RIGHT-side lines。
   - 可以阅读全文拿上下文, 但只应对 diff 中能合法锚定的位置输出 inline suggestion。

6. `review_scope = "file"` 时:
   - 先完整阅读被点名的文件。
   - 如果最佳修改点也在 diff 中, 可以输出 inline suggestion。
   - 如果最佳修改点不在 diff 中, 不要伪造锚点, 把结论写进 summary。

7. 如果没有高价值、可直接应用的修改, 返回空 comments, 并在 summary 里简要说明。

8. 如果建议里涉及多行替换, 只在你能给出完整、可直接应用的 replacement text 时才输出。

  -- Characteristic 256 means 16 * 16 = 0.
  example [CommRing α] [IsCharP α 256] (x : α) :
      (x + 16) * (x - 16) = x^2 := by
    grind

  -- Works on built-in rings such as `UInt8`.
  example (x : UInt8) : (x + 16) * (x - 16) = x^2 := by
    grind

  example [CommRing α] (a b c : α) :
      a + b + c = 3 →
      a^2 + b^2 + c^2 = 5 →
      a^3 + b^3 + c^3 = 7 →
      a^4 + b^4 = 9 - c^4 := by
    grind

  example [Field α] [NoNatZeroDivisors α] (a : α) :
      1 / a + 1 / (2 * a) = 3 / (2 * a) := by
    grind
  ```

  ### Other options

  - `grind (splits := <num>)` caps the *depth* of the search tree.  Once a branch performs `num` splits
    `grind` stops splitting further in that branch.
  - `grind -splitIte` disables case splitting on if-then-else expressions.
  - `grind -splitMatch` disables case splitting on `match` expressions.
  - `grind +splitImp` instructs `grind` to split on any hypothesis `A → B` whose antecedent `A` is **propositional**.
  - `grind -linarith` disables the linear arithmetic solver for (ordered) modules and rings.

  ### Additional Examples

  ```
  example {a b} {as bs : List α} : (as ++ bs ++ [b]).getLastD a = b := by
    grind

  example (x : BitVec (w+1)) : (BitVec.cons x.msb (x.setWidth w)) = x := by
    grind

  example (as : Array α) (lo hi i j : Nat) :
      lo ≤ i → i < j → j ≤ hi → j < as.size → min lo (as.size - 1) ≤ i := by
    grind
  ```

syntax "grind?"... [Lean.Parser.Tactic.grindTrace]
  `grind?` takes the same arguments as `grind`, but reports an equivalent call to `grind only`
  that would be sufficient to close the goal. This is useful for reducing the size of the `grind`
  theorems in a local invocation.

syntax "grind_linarith"... [Lean.Parser.Tactic.grind_linarith]
  `grind_linarith` solves simple goals about linear arithmetic.

  It is a implemented as a thin wrapper around the `grind` tactic, enabling only the `linarith` solver.
  Please use `grind` instead if you need additional capabilities.

syntax "grind_order"... [Lean.Parser.Tactic.grind_order]
  `grind_order` solves simple goals about partial orders and linear orders.

  It is a implemented as a thin wrapper around the `grind` tactic, enabling only the `order` solver.
  Please use `grind` instead if you need additional capabilities.
