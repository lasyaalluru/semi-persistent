# Kata 6 — 手跑 §2 的 use-list 工作表

## 图在 `(union c (True))` 之前

| 类 | 名字 | 结点 | 抽象值（若已有分析） | use-list |
| --- | --- | --- | --- | --- |
| c3 | three | `(Lit 3)` | `[3, 3]` | `Lt`, `Ite` |
| c10 | ten | `(Lit 10)` | `[10, 10]` | `Lt`, `Ite` |
| cB | c | `(Lt three ten)` | `unknown`（Lt 没有登记 transfer） | `Ite` |
| cT | t | `(Ite c three ten)` | `[3, 10]` = join(then, else) | （空，Clamp 还没建） |

`True` 还不在图里。

## `(union c (True))` 之后，重算顺序

1. 建立 `(True)`，它自己的类值是 `true`。
2. 把这个类与 `c` 合并。幸存类写入 `meet(unknown, true) = true`。这是一次严格收紧。
3. `c` 的 use-list 里只有 `Ite`。把 `Ite` 推进分析工作表。
4. 重算 `make(Ite)`：条件现在是 `true`，选 then 臂 → `[3, 3]`。
5. `meet([3, 10], [3, 3]) = [3, 3]`。`t` 收紧。
6. `t` 的 use-list 此时仍空，工作表排空。
7. **没有新结点，没有别的类被合并。** `t` 的收紧必须单独进入半朴素 delta，否则后面的 `within` 守卫看不到。

Clamp 是在 union **之后**才加入的。所以这一步被重算的只有 `Ite`，不是 `Clamp`。

## FINDINGS.md #1 和 #7

当前 `yaspar-org/semi-persistent` 的 `main`（2026-08-31 克隆）里 **没有** `egraph/stress/FINDINGS.md`，也没有 `stress/` 目录。提案写的路径已经不在树上。

用设计文档代替这两条对类值的影响：

- **Canonization 不稳定（提案说的 #1–#3 一类）**  
  `egraph/doc/design/04-canonization.md`：孩子类一合并，结点的规范形依赖「什么时候 build」。分析如果只在 merge 时重算、不在 recanonize 时重算，类上的格值会是错的，不只是更粗。
- **原子既没有被调度降下来（提案说的 #6 一类，守卫版是 #7 的邻居）**  
  `EGRAPH_DUMP_PLAN` 的注释写在 `egraph/src/schedule.rs`：曾经有过 Join 排在 ExpandA 之后、把变量清掉的缺陷。对抽象守卫，同类 bug 的表现是：守卫原子没有对应 Step，改写无条件开火。这就是 Task 3 要加的 P6。

结论：类值必须在 **merge 和 recanonize** 两条触发器上重算；守卫必须有且仅有一个 Step。缺了前者，值是脏的；缺了后者，改写是不许可的。
