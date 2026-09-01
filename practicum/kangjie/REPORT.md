# 第 1–2 周热身报告

课题：Lattice Semantics for E-Graphs，附在 `yaspar-org/semi-persistent`。  
热身按提案 §1.6，六项都留成回归，不扔草稿纸。

## 怎么跑

```bash
cd ramp-up
cargo test
```

六项对照测试都在这个 crate 里。Verus 合同在 `verus/interval_u8.rs`，要在钉住的 Verus `0.2026.08.02.b677dd5` 下再跑 `cargo verus verify`。没装 Verus 之前，Rust 测试是同一条命题的可执行影子，**不能代替门禁**。

`.egg` 文件要用引擎二进制跑：

```bash
# 在克隆下来的 semi-persistent 仓库里
cargo build --release -p semi-persistent-egraph
EGRAPH_DUMP_PLAN=1 ./target/release/semi-persistent \
  --union-by size path/to/ramp-up/egg/section2_classic.egg
```

今天的基线（2026-08-31 的 `main`）：没有 `(domain …)`，没有 `:abstract`，没有 `within`。`section2_classic.egg` 会在解析/resolve 阶段对 `within` 报错。引擎对 §2 **什么格分析都不做**。这就是提案要我们记下来的“今天什么都不做”。

## Kata 1 — 并查集、hash-cons、rebuild

- `src/union_find.rs`：路径压缩 + 按秩合并，对拍朴素的集合划分。
- `src/egraph.rs`：`add` / `find` / `union` / `rebuild`。
- 关掉 rebuild：子类合并后 hash-cons 仍留着旧孩子键，下一次 `Add` 会再分配一个结点。这就是 rebuild 存在的理由。

`cargo test kata1` 覆盖这三条。

## Kata 2 — 饱和、发散、`--union-by`

| 文件 | 行为 |
| --- | --- |
| `egg/saturate.egg` | 加法交换。第二次 `(run 10)` 不再长图。 |
| `egg/diverge.egg` | `(F x) → (F (S x))`。不设 fuel 就不停。 |
| `egg/union_by.egg` | 一串 union。语义检查在 size/uses/sum 下应一致；幸存类和 recanon 顺序会变。 |

`EGRAPH_DUMP_PLAN=1` 打在 stderr 上，格式是 `egraph/src/schedule.rs` 里的 `step[i]: Join|ExpandA|CheckPred|…`。§2 今天还没有抽象守卫 Step；加上 `within` 之后，计划里必须出现恰好一个对应 Step（Task 3 的 P6）。

## Kata 3 — u8 区间的 `has` 和 `add`（门禁）

`Interval { lo, hi }`，`wf` 是 `lo ≤ hi`，`has(x)` 是 `lo ≤ x ≤ hi`。  
`add`：端点和不溢出就用端点和；否则回 `top`。  
合同：`has(x) ∧ has(y) ⇒ result.has(x.wrapping_add(y))`。回 `top` 仍然成立，因为 `top` 含所有 `u8`。

没有对着 `domains.rs` 写。和仓库里现有 Interval 的差别：那边没有 bottom，不相交的 meet 只能回 top。

## Kata 4 — meet 定律，再加 ⊥（门禁）

先做没有 bottom 的 meet：`[3,3] ⊓ [10,10] = top`。吸收律 `meet(a, top) = a` 立刻坏掉。  
加上 `Bottom` 之后重证：幂等、交换、结合、`meet(a, top) = a`、`meet(a, bottom) = bottom`。  
`add` 的单调性比 meet 交换难：要沿两个端点分别推。这就是 §3.1 的缩微版。

## Kata 5 — 从 well-formedness-only 里挑减法（门禁 / Task 1 估时）

`proof-status.md`（2026-08-21）写明：Interval 上有普遍包含合同的只有 `add`、`meet`、`join`、`div_const`。减法、乘法、移位、按位运算只有良构。

我给 `sub` 补了包含后条件：`has(x) ∧ has(y) ⇒ result.has(x.wrapping_sub(y))`，端点下溢回 top。

能证到哪：

- 两端都不下溢：用无符号减法的单调性，和 `add` 同一套路。
- 两端都下溢：结果是 top，包含是显然的。
- **卡在**：只有一端下溢、具体差却 wrapping 的那一支。要多写几个 wrapping lemma。
- 区间除法的三分零测试（`interval-extensions.md` §1）更重，这就是 Task 1 前半的工作量。

估时：减法这种“缺的 transfer”按天计；带 alarm 的除法加 bottom 按周计。这和提案周 3–5 的安排一致。

## Kata 6 — 手跑工作表

见 `kata6-trace.md`。`(union c (True))` 之后重算的是 `Ite`，不是 `Clamp`。`t` 从 `[3, 10]` 收到 `[3, 3]`，必须进 delta。

`stress/FINDINGS.md` 不在当前 `main`。用 `04-canonization.md` 和 `schedule.rs` 的计划转储说明：漏掉 recanonize 触发会得到脏值；漏掉守卫 Step 会得到未许可的改写。

## 热身结束的标志

- [x] 六项都变成仓库里的测试或文稿
- [x] §2 写成 `.egg`，记下今天引擎对它做什么（对 `within` 报错 / 不做格分析）
- [ ] Kata 3–5 在钉住的 Verus 下 `cargo verus verify` 通过 — 装好 pinned Verus 后把 `verus/interval_u8.rs` 接进 `abstract-domains` 再跑
- [ ] 用引擎二进制带 `EGRAPH_DUMP_PLAN=1` 跑一遍 `section2_classic.egg`，把 stderr 贴进本报告

第三、四条是门禁的剩余动作，依赖本机的 Verus 和 `rustc 1.97.1`。逻辑和回归已经在这个目录里。
