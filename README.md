# QCP LiteOS 双向链表验证复现

数理逻辑大作业第六题：**QCP: A Practical Separation Logic-based C Program Verification Tool（TASE 2026）**。

基于作者 **QCP v1.0** 工件，复现 LiteOS 链表的**初始化、插入、删除三个案例**，保留带规约的 C 源码、完整 Rocq/Coq 证明、必要证明库、运行脚本和验证证据，并对照固定版本的 OpenHarmony 实现。成果与使用方法以本 README 为入口。

## 复现成果

三个输入文件覆盖五个函数、16 项直接验证条件：**复用作者 7 项证明，补全 9 项证明，全部以 `Qed` 完成，直接证明中无 `Admitted`**。仓库保存的完整运行记录来自 **2026-10-26**，包括重新生成目标、从零编译 133 个模块和 172 项传递假设查询。

| 案例 | 函数 | 验证条件数 | 作者原有证明 | 补全证明 |
| --- | --- | ---: | ---: | ---: |
| 初始化 | `LOS_ListInit` | 1 | 1 | 0 |
| 插入 | `LOS_ListAdd` | 2 | 2 | 0 |
| 插入 | `LOS_ListTailInsert` | 4 | 2 | 2 |
| 插入 | `LOS_ListHeadInsert` | 2 | 0 | 2 |
| 删除 | `LOS_ListDelete` | 7 | 2 | 5 |
| **合计** | **五个函数** | **16** | **7** | **9** |

补证集中在 [List_Add_proof_auto.v](src/SeparationLogic/examples/LiteOS/List_Add_proof_auto.v) 和 [LOS_ListDelete_proof_auto.v](src/SeparationLogic/examples/LiteOS/LOS_ListDelete_proof_auto.v)。仅修改这两份文件的证明体，C 实现、规约、目标定义、检查接口和作者手动证明保持固定工件内容。**`proof_auto.v` 沿用作者命名，其中九项补证是编写的 Coq 证明，不能按文件名计作 SMT 自动证明。** 逐项入口及方法见 [命题证明索引](docs/命题证明索引.md)。

| 检查内容 | 保存的结果 | 证据 |
| --- | --- | --- |
| QCP 生成 | 三个案例成功；生成目标及接口按 LF 归一后与固定文件一致 | [generation.json](evidence/generation.json) |
| Coq 编译 | 从无编译产物开始编译 133 个模块，三个 `goal_check` 通过 | [构建状态](evidence/build.status.json)、[模块记录](evidence/compiled-modules.json) |
| 假设审计 | 16 项直接目标、35 项共享策略；172 项查询覆盖 121 个实际模块成员 | [逐目标结果](evidence/vc-status.md)、[查询索引](evidence/assumptions.json) |
| OpenHarmony 对照 | 五个函数、12 条有序语句；10 条 token 相同，2 条仅空指针写法不同 | [comparison.json](evidence/comparison.json) |

完整统计见 [summary.json](evidence/summary.json)。这些日志记录已有的完整运行；新的验证按下文命令执行。

## 案例与前后置条件

本项目验证 Hoare 三元组 `{P} C {Q}`：在 `P` 提供的内存资源和结构约束下执行函数，满足相应安全要求及后置条件 `Q`。`store_dll(storeA, head, L)` 表示以 `head` 为哨兵、抽象节点序列为 `L` 的循环双向链表，`storeA` 描述节点关联的数据资源。`*`（Coq 中的 `**`）组合互不重叠的堆资源；`undef_data_at` 表示拥有字段权限而不约定原值。指针非空不能代替字段权限。

下表是行为摘要，精确定义以链接的 C 规约及 Coq 目标为准。

| 案例与源码 | 前置条件 | 后置条件与效果 |
| --- | --- | --- |
| [初始化](src/QCP_examples/LiteOS/LOS_ListInit.c) | 拥有哨兵的 `pstPrev`、`pstNext` 两个可写字段 | 两字段指向自身，得到空链表 `store_dll(storeA, list, nil)` |
| [插入](src/QCP_examples/LiteOS/List_Add.c) | 低层规约提供锚点、原后继及新节点的局部资源；高层规约提供原链表和新节点资源 | `LOS_ListAdd` 在锚点之后插入；以哨兵为锚点时，抽象序列从 `L` 变为 `node :: L`；尾插为 `L ++ [node]` |
| [删除](src/QCP_examples/LiteOS/LOS_ListDelete.c) | 低层规约提供待删节点及邻接资源；中层规约用前后链段描述其位置 | 前驱和后继重新连接；中层序列从 `L1 ++ [node] ++ L2` 变为 `L1 ++ L2`，保留被删节点字段权限和数据资源 |

插入的四条赋值顺序为：

```c
node->pstNext = list->pstNext;
node->pstPrev = list;
list->pstNext->pstPrev = node;
list->pstNext = node;
```

若原后继为 `x`，最终局部连接为 `list <-> node <-> x`。证明整体链表有效还需保留未修改资源，并用 `dllseg`、`dllseg_shift` 等链段引理重新组合 `store_dll`。头插调用 `LOS_ListAdd(list, node)`，尾插调用 `LOS_ListAdd(list->pstPrev, node)`，均包含在插入案例中。

删除实现修复邻接关系后把两个链接字段置零；规约只要求这些字段仍可用，不要求保留具体值。摘链不包含 `free`；初始化和插入也不分配内存。

## 符号执行、SMT 与 Rocq 的作用

```mermaid
flowchart LR
    C[带规约的 C 程序] --> Q[QCP 符号执行]
    Q --> S[分离逻辑规则与轻量 SMT]
    S --> G[Coq 目标与证明接口]
    G --> P[作者证明与补全证明]
    P --> K[Coq 内核检查 goal_check]
    K --> A[Print Assumptions 依赖审计]
```

| 环节 | 职责 | 本项目中的对应 |
| --- | --- | --- |
| 符号执行 | 沿语句更新符号状态，产生字段访问、调用和返回等验证义务 | 三个输入对应的 `*_goal.v` |
| 分离逻辑规则引擎 | 匹配字段资源，应用谓词及策略，整理堆断言 | `store_dll`、链段谓词和共享策略 |
| 内置轻量 SMT | 处理线性整数算术（LIA）与未解释函数（UF）组成的纯约束；论文所述版本不支持量化公式 | 常量范围和等式属于适用问题；堆资源及链段拼接还需分离逻辑推理 |
| Rocq/Coq 后端 | 完成剩余目标，检查证明项和接口实现 | `*_proof_*.v` 与三个 `*_goal_check.v` |

工具分工依据 [论文第 4.2、4.3 节](https://arxiv.org/html/2505.12878v3#S4.SS2)。16 项导出目标分为：5 项返回条件、6 项资源整理、2 项算术安全条件、1 项谓词展开、2 项规约派生。

删除的 `LOS_ListDelete_safety_wit_1/2` 要求 `INT_MIN <= 0 <= INT_MAX`，属于简单算术条件；本仓库实际用 **Coq 的 `entailer!; lia` 补证**。初始化要把自指向字段折叠为空链表；插入和删除的规约派生要使用递归谓词及链段引理。

**当前证据没有逐条 SMT 调用轨迹，不能给出“SMT 自动完成多少项”的比例。** `entailer!` 是分离逻辑 tactic，`lia` 是 Coq 算术 tactic，均不等同于调用 QCP 内置 SMT。`goal_check` 检查目标是否有对应证明，再以 `Print Assumptions` 检查传递依赖。

## 与 OpenHarmony 实现对照

参考源码固定于 `kernel_liteos_a` 提交 [`4ac7f3aed67000b47bc14d6fe79d63ada708d780`](https://github.com/openharmony/kernel_liteos_a/tree/4ac7f3aed67000b47bc14d6fe79d63ada708d780)，本地文件见 [los_list.h](references/openharmony/los_list.h)。结构体字段顺序均为 `pstPrev`、`pstNext`，五个函数的参数和有序语句均已比较。

| 函数 | 语句数 | 对照结果 |
| --- | ---: | --- |
| `LOS_ListInit` | 2 | 两条赋值去注释后 token 相同 |
| `LOS_ListAdd` | 4 | 四条赋值及顺序相同 |
| `LOS_ListTailInsert` | 1 | 尾插调用相同 |
| `LOS_ListHeadInsert` | 1 | 头插调用相同 |
| `LOS_ListDelete` | 4 | 两条邻接更新相同；置空分别使用 `(LOS_DL_LIST *)0` 与 `NULL` |

共 12 条语句，含 10 次赋值和 2 次调用。脚本仅对应删除函数两条置空语句的空指针写法，保留其他 token 和语句顺序。结果见 [comparison.json](evidence/comparison.json)，实现见 [compare_sources.py](scripts/compare_sources.py)；参考目录同时保留类型、工具链和构建宏头文件。

## 复现办法

全部命令在仓库根目录执行，脚本只使用 Python 标准库。详细下载、工具路径、输出和排错方法见 [复现说明](docs/复现说明.md)。

### 1. 核验已有成果

只需 **Python 3.10+**，无须 QCP、Coq 或网络：

```bash
python3 -B scripts/reproduce.py check
```

Windows PowerShell 使用已安装的 Python 3.10+：

```powershell
python -X utf8 -B scripts/reproduce.py check
```

`check` 验证文件清单、源码身份、证明覆盖、保存的编译及假设记录和 OpenHarmony 对照。返回 `0` 表示**当前文件与保存证据一致**，不重新运行 QCP 或编译 Coq。

### 2. 完整重跑

环境：**Ubuntu 22.04/24.04、Linux x86_64、Python 3.10+、GNU make、Coq 8.20.1、OCaml 4.14.2**。Windows 用户可在 WSL 的 Ubuntu 中进入仓库，例如当前目录为 `cd /mnt/d/cnm/-`。

首次准备需要联网，以有 `sudo` 权限的普通用户执行：

```bash
bash scripts/setup-ubuntu.sh
python3 -B scripts/reproduce.py full --jobs 2
```

已有兼容工具链和固定 QCP 时，直接指定路径：

```bash
python3 -B scripts/reproduce.py full \
  --coq-bin /path/to/opam-switch/bin \
  --qcp-bin /path/to/symexec \
  --jobs 2
```

`full` 重新运行三个 QCP 输入，核对生成目标及接口，恢复完整证明，从零编译 133 个模块，执行 172 项假设查询和源码对照。每次结果写入新的 `runs/时间戳/`。

### 3. 仅重新检查 Coq 证明

```bash
python3 -B scripts/reproduce.py build \
  --coq-bin /path/to/opam-switch/bin \
  --jobs 2
```

`build` 省略 QCP 生成，同样执行纯源码编译和假设审计。默认工具链为 `.tools/coq/_opam/bin/`，QCP 为 `.tools/qcp/symexec`。

成功结果：`summary.json` 中 `status = passed`、`vc_count = 16`、`admitted = 0`、`fresh_compiled_modules = 133`、`assumption_queries = 172`。完整模式 `qcp_rerun = true`；仅构建模式为 `false`。

## 仓库目录

| 路径 | 内容 |
| --- | --- |
| [src/QCP_examples/LiteOS/](src/QCP_examples/LiteOS/) | 三个带规约的 C 案例 |
| [src/SeparationLogic/examples/LiteOS/](src/SeparationLogic/examples/LiteOS/) | 验证目标、完整证明、检查接口和链表模型 |
| `src/SeparationLogic/` 其他子目录 | 构建所需证明库，共保留 133 份 `.v` 源码 |
| [references/openharmony/](references/openharmony/) | 固定提交的四份参考头文件 |
| [scripts/](scripts/) | 环境准备、工件下载、复现、审计和源码对照 |
| [docs/复现说明.md](docs/复现说明.md) | 详细命令、环境、验收和排错 |
| [docs/命题证明索引.md](docs/命题证明索引.md) | 16 项目标的证明入口、来源和方法 |
| [evidence/](evidence/) | 完整运行的文本证据、逐项假设和对照结果 |
| [sources.lock.json](sources.lock.json) | 固定来源、工具版本及源码/工件 SHA-256 |
| [MANIFEST.sha256](MANIFEST.sha256) | 交付文件完整性清单 |
| [licenses/](licenses/) | 来源说明和相关许可证 |

建议先读初始化规约及证明，再按索引阅读插入、删除，最后查看日志和假设依赖。仓库可独立拷贝使用；`.tools/`、`runs/` 和编译产物在运行时生成，不进入 Git。

## 验证范围与来源

证明依赖选定规约和逻辑模型。传递假设并集为标准库函数外延性、命题外延性和框架地址求值参数 `SimpleC.SL.CNotation.eval_addr_expr`，声明见 [assumption-catalog.json](evidence/assumption-catalog.json)。直接证明无 `Admitted` 不代表整个框架无假设。

源码对照覆盖固定版本的这五个函数，未验证所有宏配置、平台 ABI 或整个内核。保存的完整链路使用已有兼容工具链；环境安装脚本未在空系统中再次验收。

- 论文：[arXiv:2505.12878](https://arxiv.org/abs/2505.12878)。
- 指定工件：[QCP v1.0 release](https://github.com/QinxiangCao/QualifiedCProgramming/releases/tag/v1.0)，固定提交 [`af71be03bdbfad353542c38013b1e69d124cb56c`](https://github.com/QinxiangCao/QualifiedCProgramming/tree/af71be03bdbfad353542c38013b1e69d124cb56c)。
- 作者仓库：[QualifiedCProgramming](https://github.com/QinxiangCao/QualifiedCProgramming)。复现以本仓库锁定的 v1.0 为准。
- 源码版权和第三方许可见 [licenses/README.md](licenses/README.md)，原文件声明予以保留。
