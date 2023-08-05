# 基于依赖类型论的定理证明器实现简介

本文旨在介绍一些有关基于依赖类型论的定理证明器实现的经典技术、问题、定义与例子。
由于编写时间与篇幅受限，且存在相关材料已经给出了经典的论述，定义与例子的叙述会相对不详细与形式化。此时需要从所引用的文本中阅读对应的内容。
依赖类型论为实现更接近日常数学所用的定理证明器提供了新的基础。「命题即类型，证明即程序，证明化简即程序求值」的对应为数学语言与计算机语言的合一化提供了自然的形式化思路。[Propositions as Types](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf)

从而，检查证明步骤的正确性的问题便转化为了检查程序类型的工作。

依赖类型论的程序类型检查并不容易，需要相对较久的时间：

- 类型检查中涉及求值操作
- 应当允许用户在一些地方不将类型写完全或省略类型
- 无处不在的依赖类型模式匹配
- 常使用 ad-hoc 多态
- 常使用 tactics 来生成 terms
- 较为复杂的类型论（如同伦类型论的可计算解释的实现）有关原始对象的操作是非平凡的
  [A new “Brunerie number”, might be easier to calculate?](https://thehighergeometer.wordpress.com/2021/09/14/a-new-brunerie-number-might-be-easier-to-calculate/)

也有一些在数学上较为成功的定理证明器是基于非依赖类型论的，或者说，相对「简单」的类型论。[Formalising Mathematics In Simple Type Theory](https://arxiv.org/abs/1804.07860)

由于它们的实现关注点与基于依赖类型论的定理证明器有较大差别，在本文中我们不会介绍。
另外，一些比较经典的编译器议题虽然会影响定理证明器的性能与运行速度，但由于太通用或已经被研究较深（如
parsing），在本文中也不会加以介绍。

本文对技术的介绍有一定的选择性，能达到同样目的的多个手段可能只会介绍一个。本文关注技术手段在当下流行的定理证明器中的具体实现。
基于各种依赖类型论变体的 Coq、Agda、Lean
都是当下相对流行，且在数学上取得一定成就的定理证明器。效率与表达能力也是它们关心的主要议题之一。
在下面的介绍中，或多或少会出现它们发展的轨迹。

## 主要环节

我们在这里使用「环节」而不是「流程」，是因为这些概念可能是同时或重叠发生的。由于文本总是线性的叙述，我们从「不清楚类型检查是什么」的设定开始介绍。

我们所讨论的的技术主要适用于实现
[Martin-Löf type theory](https://plato.stanford.edu/entries/type-theory-intuitionistic/)（MLTT）及变体。有关介绍
MLTT 的内容浩如烟海，可以参考主流的一些类型论教材。在实现更为复杂的类型论，如
[Cubical Type Theory](https://arxiv.org/abs/1611.02108)
时，虽然本文介绍的内容仍然有相当大一部分能适用，但一些额外的实现需求与策略也需要注意。[cctt](https://github.com/AndrasKovacs/cctt)

此外，有一些关于 MLTT 及变体实现相关性能研究的资料：

- [Normalization Bench](https://github.com/AndrasKovacs/normalization-bench)
- [smalltt](https://github.com/AndrasKovacs/smalltt)
- [sixty](https://github.com/ollef/sixty)

### Typing

类型检查关注一个给定的项 $x$ 在给定的上下文 $\Gamma$ 中是否属于一个给定的类型
$A$，计作 $\Gamma \vdash x : A$。 类型检查是通过将推演规则（derivation
rules）应用到语法上，得到完整推演过程的机械化操作，可以使用算法进行描述。
最简陋的类型检查算法只关心推演规则中每个类型的形成规则、引入规则与消去规则（与必要的逻辑规则，如上下文有关的操作）。简单的类型检查的例子参见
[Type Theory and Formal Proof, Ch2 Sec8 Type Checking in $\lambda_{\to}$](https://www.cambridge.org/core/books/type-theory-and-formal-proof/0472640AAD34E045C7F140B46A57A67C)
与
[Programming Language Foundations in Agda: Lambda](https://plfa.github.io/Lambda/)；
较为先进的类型检查算法除了能自动插入一些隐式参数与根据上下文求解用户没有显式写出的内容。
因此，除了每个类型的形成规则、引入规则与消去规则外，较为先进的类型检查算法还关心推演规则中的一些有关类型的其他性质。

非形式化地讲，在相对简单的类型理论 —— 如 $\lambda_{\to \times \mathbb
N}$（即有函数类型、Cartesian 积与自然数的类型论）——
中，去描述类型检查的过程是相对容易的。 例如，对于项 $f := \lambda (x, y) . (y,
0)$，要检查 $\Gamma, x : \mathbb N, y : \mathbb N \vdash f : \mathbb N \times
\mathbb N \to \mathbb N \times \mathbb N$，即写出它的完整推演：

- 对于 $0$，考虑 $\mathbb N$ 的引入规则，有 $\empty \vdash 0 : \mathbb N$
- 对于 $y$，由于上下文中有 $y : \mathbb N$，有 $y : \mathbb N \vdash y : \mathbb
  N$
- 对于 $(y, 0)$，考虑 $\times$ 的引入规则 $(\_,\_)$，有 $y : \mathbb N \vdash
  (y, \_) : \mathbb N \times \_$，进一步有 $y : \mathbb N \vdash (y, 0) :
  \mathbb N \times \mathbb N$
- 对于 $\lambda (x, y) . (y, 0)$，由于 $y : \mathbb N \vdash (y, 0) : \mathbb N
  \times \mathbb N$，考虑 $\to$ 的引入规则 $\lambda$ 与 $\times$ 的引入规则
  $(\_,\_)$，有 $x : \mathbb N, y : \mathbb N \vdash (x, y) : \mathbb N \times
  \mathbb N$，进一步 $x : \mathbb N, y : \mathbb N \vdash \lambda (x, y) . \_ :
  \mathbb N \times \mathbb N \to \_$，进一步有 $\Gamma, x : \mathbb N, y :
  \mathbb N \vdash f : \mathbb N \times \mathbb N \to \mathbb N \times \mathbb
  N$

对于项 $\mathrm{xs} : \mathbb N \times \mathbb N$，要检查 $\Gamma \vdash f\
\mathrm{xs} : \mathbb N \times \mathbb N$，只需要考虑 $\to$ 的消去规则。

从上面的例子，我们可以注意到：

- 在简单的类型系统中，复杂的类型是由基础类型（此处为 $\mathbb
  N$）、类型构造子（此处为分别接受两个参数的 $\to$ 与
  $\times$），通过有限次应用组合而成。对应的类型检查也跟随组合的风格，首先对
  subterm 进行检查，再应用推演规则来组合成完整的推演过程。

- 一些项即使不标注类型，我们也能合成出它所属于的类型。这样的操作被称为类型合成。考虑这样的表述：对于
  $\Gamma \vdash x : A$，如果三元组 $(\Gamma, x, A)$
  的所有元素都被给出，写出完整推演过程被称为类型检查；如果缺失类型 $(\Gamma, x,
  \_)$，写出合成缺失类型的推演过程被称为类型合成。类型检查与类型合成合称
  typing。在这一领域有优秀的综述
  [Bidirectional Typing](https://arxiv.org/abs/1908.05839)。有关 typing
  理论的一个重要推论是，易用定理证明器的 typing 能力需要满足用户只需要显式为
  top-level
  的定义与引入规则消除规则相接出现的定义标注类型，其他部分项定义的类型可以不用被标注。

综述 Bidirectional Typing 与同名的 typing
策略指出，一些项的类型是适合被检查的，一些项的类型是适合被合成的。当需要检查
$\Gamma \vdash x : A$ 时，如果其中的 $x$
是适合类型合成的项，则会采取首先合成一个类型 $A'$，再比较 $A$ 与 $A'$
是否相等。于是，我们需要定义类型的相等。在简单的类型系统中，类型的相等定义跟随之前所描述的类型检查相同的组合风格，即结构化的比较是否是由相同的类型构造子所构造，递归比较参数是否相等。在依赖类型论的定理证明器中，情况变得复杂：由于我们有对类型做语法抽象操作的能力（$\Pi$-types），我们需要处理非
closed term；由于在依赖类型论中，常常有形如 $A : \mathcal U$
的设定，我们在推演系统中无需为类型的相等添加新的
judgement，我们也可以定义类型上的函数，通过函数应用获得输出的类型。类型的相等定义变得非平凡，一个朴素的想法是我们可以比较已经被充分做
reduction 后的类型，或者说，进行 normalise 后的结果。

### Evaluation

论文
[A simple type-theoretic language: Mini-TT](https://www.cambridge.org/core/books/abs/from-semantics-to-computer-science/simple-typetheoretic-language-minitt/21451A12E2E24A1F51C82421B066824A)
为一般的依赖类型论语言/定理证明器提供了定义判断类型相等算法的思路，即
Normalisation by Evaluation（NbE）：语法域与语义域被分离，语法上的 open term
在语义中也有了对应的表示；操作 $\mathtt{eval}$
在给定的环境下将语法域元素映射到语义域，操作 $\mathtt{readback}$
将给定的自由变元集与语义域元素映射到语法域。求语法域元素的 normal form 即操作
$\mathtt{eval}$ 与 $\mathtt{readback}$ 的组合。注意这些操作都允许非 closed term
存在，由于我们有对类型做语法抽象操作的能力，比较 open terms
是否可相互转换是不可避免的。现在，我们可以定义一般的依赖类型论语言/定理证明器中类型的判断相等操作
$\mathtt{conv}$。注意 $\mathtt{conv}$ 不需要一个 term 达到 normal
form，而只需要结构化地比较语义域元素元素是否相等。

一个立方类型论的实现 [cubicaltt](https://github.com/mortberg/cubicaltt) 正是基于
Mini-TT 而作。

NbE 的语义基础参见
[Normalization by Evaluation Dependent: Types and Impredicativity](https://www.cse.chalmers.se/~abela/habil.pdf)。也有许多优秀的
NbE 实现教程，如
[Checking Dependent Types with Normalization by Evaluation](https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf)、[Elaboration Zoo](https://github.com/AndrasKovacs/elaboration-zoo)。

#### 值的表示

依赖类型论语言/定理证明器的 core terms 求值过程往往接近 untyped
$\lambda$-calculus 的求值过程。
这是由于在通过类型检查后，类型的形成规则、引入规则、消除规则的出现都是符合类型系统规则的；且求值时，类型的形成规则、引入规则被翻译成语义域值的构造器，类型的消除规则被翻译为在被消除的项是值时计算出符合语义的结果、在被消除的项是
neutral terms 时构造更大的 neutral terms 的过程。从而，此处 core terms
的求值过程与 untyped $\lambda$-calculus 是接近的，但是如果要达到 normal form，在
$\mathtt{readback}$ 时还需要按照类型信息将项变换到 canonical form。

而 $\lambda$-calculus 演算的各种求值策略与概念也被广泛研究。 在描述
$\lambda$-calculus 的语义域时需要注意 $\lambda$ term 的 body
是可能且常常出现捕获情况的，常用的处理如： 使用高阶抽象语法（HOAS）实现
$\lambda$-calculus 将 $\lambda$ terms 直接翻译为 host language
的函数对象（如匿名函数），higher-order 即是这里 host language 的函数；使用
closure 实现将 $\lambda$ terms 翻译为携带环境的 open
term。对应的函数应用的实现是自然的。

理论基础：[A Functional Correspondence between Evaluators and Abstract Machines](https://www.brics.dk/RS/03/13/BRICS-RS-03-13.pdf)

参考实现：[Elaboration Zoo](https://github.com/AndrasKovacs/elaboration-zoo)

目前依赖类型定理语言/证明器中较为标准的实现是 closure 表示的变体，这是由于

- object language 中函数相等的定义更容易表达
- 常用 host languages 中的函数对象无法序列化或打印
- closure 实现更容易实现一些传统的编译器优化技术

等原因。

### Unification

易用的定理证明器应当允许用户省略一些类型标注、实例标注并提供自动参数和自动证明
absurd pattern 等功能。Typing、Unification、Pattern Matching、Typeclass
Resolution 等环节都实现了一定的相关功能。

最简单的 unification
问题可以从这样的需求出发：我们希望用类型来引导程序的设计，未完成的程序被称为洞、有时我们想要省略一些类型标注、有时我们希望能使用策略来让定理证明的语言更加贴近自然的思维模式。[Type-Driven Development with Idris](https://www.manning.com/books/type-driven-development-with-idris)

最简单的 unification 的问题是 pattern unification。考虑这样的例子：要求解等式
$?\alpha\ \mathrm{spine} = \mathrm{RHS}$，如果有

- $\mathrm{spine}$ 由不同的受约变元组成
- $\mathrm{RHS}$ 中的自由变元都在 $\mathrm{spine}$ 中
- 元变元 $?\alpha$ 不在 $\mathrm{RHS}$ 出现

这样的 unification
问题求解相对较为简单，能求解的问题类别也相对受限。[Elaboration Zoo](https://github.com/AndrasKovacs/elaboration-zoo/blob/master/03-holes/pattern-unification.txt)

更复杂的 unification 问题往往是不可判定的，如 higher-order unification。论文
[Unification of Simply Typed Lambda-Terms as Logic Programming](https://www.lfcs.inf.ed.ac.uk/reports/91/ECS-LFCS-91-160/)
指出了一些可判定的部分（也是 pattern unification 中 pattern 一词的来源，pattern
fragment），并且陈述：

> The unification of simply typed λ-terms modulo the rules of β- and
> η-conversions is often called “higher-order” unification because of the
> possible presence of variables of functional type.

> In order to avoid using the very vague and over used adjective “higher-order”,
> we shall refer to the problem of unifying simply typed λ-terms modulo β- and
> η-conversion as βη-unification.

有关这类更复杂的 unification 问题参见
[Higher-Order Dynamic Pattern Unification for Dependent Types and Records](https://www.cse.chalmers.se/~abela/unif-sigma-long.pdf)。同时它也是
Agda 实现 unification 的理论参考。此外，一个有趣的原型参见
[Functional Pearl: Dependent type inference via free higher-order unification](https://arxiv.org/abs/2204.05653)。

### Pattern Matching

当我们要归纳地去引入一个类型时
[Homotopy Type Theory, Remark 1.5.1. There is a general pattern for introduction of a new kind of type in type theory](https://homotopytypetheory.org/book/)，定义这个类型，也就是说：

1. formation rules
2. introduction rules
3. elimination rules
4. computation rule
5. (optional) uniqueness principle

例如，考虑我们如何定义自然数类型，并且使用这里定义的类型来定义新操作与证明操作相关的性质。(可以观察在
Coq 中 inductive 地声明一个 type 后，它自动生成了哪些定义)

[Symmetry, 2.4 The type of natural numbers](https://unimath.github.io/SymmetryBook/book.pdf)

直接使用 induction principle
来写定义与作证明相对比较繁琐，许多简明的形式也无法展现。 在
[Homotopy Type Theory,, 1.10 Pattern matching and recursion](https://homotopytypetheory.org/book/)
描述了一种简洁的记法，即模式匹配。

模式匹配是一系列机械化的方法，将定义等式翻译为类型的消除规则。但在实现上有多种候选，如
case tree 等。 在翻译定义等式的过程中也有一系列重要问题，如

- 停机检查
  [foetus – Termination Checker for Simple Functional Programs](https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.44.3494&rank=1)
- 覆盖检查
- datatype indices 的 unification

等。

理论基础：[Dependent pattern matching and proof-relevant unification](https://jesper.sikanda.be/files/thesis-final-digital.pdf)

参考实现：[Tiny Idris](https://github.com/edwinb/SPLV20)

### Typeclass Resolution

理论基础：[Tabled Typeclass Resolution](https://arxiv.org/abs/2001.04301)

### Tactics and Metaprogramming

论文
[Idris, a General Purpose Dependently Typed Programming Language: Design and Implementation](https://www.type-driven.org.uk/edwinb/papers/impldtp.pdf)
中描述了依赖类型定理语言/证明器的 IR 分层与基础 tactics 的实现。论文
[Elaborator Reflection: Extending Idris in Idris](https://www.type-driven.org.uk/edwinb/papers/elab-reflection.pdf)
是前篇论文的后续工作，此外在 _Related Work_ 一节给出了有关 Tactics and
Metaprogramming 相关其他工作的论述。

## 经典的优化手段

### Erasure

有些 term 在运行时不需要具体的表示。一个经典的例子是
[Inductive Families Need Not Store Their Indices](http://www.e-pig.org/downloads/indfam.pdf)。

Idris 1 的编译器有判断 term 是否可以被 erasure 的机制
[Erasure By Usage Analysis](https://docs.idris-lang.org/en/latest/reference/erasure.html)。Idris
2 的类型系统加入了一些新的原语
[Idris 2: Quantitative Type Theory in Practice](https://arxiv.org/abs/2104.00480)。Agda
也提供了类似的标记机制
[Run-time Irrelevance](https://agda.readthedocs.io/en/latest/language/runtime-irrelevance.html)。

### Incremental Reparse

实现增量语法解析需要语法设计本身具有一些不变量，保证语法在一定单元内修改不会影响全局状态的合法性与解析结果不变。此外，选择合适的数据结构来表示语法树能使得修改操作相对低复杂度。[rowan](https://docs.rs/rowan/latest/rowan/)

在定理证明器中常常出现 macros
或其他元编程类似物，在实现增量语法解析式也需要加以考虑。[Macros vs incremental parsing](https://internals.rust-lang.org/t/macros-vs-incremental-parsing/9323)

### Incremental Computation

许多传统语言编译器编译器被设计为 pass 构成的 pipeline。
交互式定理证明器有着编辑器交互性强、需要提供交互工具、常常需要增量计算修改、类型检查相对困难等特点。
在设计交互式定理证明器架构时就需要充分考虑到这些特点与困难。

[Query-based compiler architectures](https://ollef.github.io/blog/posts/query-based-compilers.html)

[Durable Incrementality](https://rust-analyzer.github.io/blog/2023/07/24/durable-incrementality.html)

### Builtin

[Agda Built-ins](https://agda.readthedocs.io/en/latest/language/built-ins.html)

[Lean Builtin Types](https://leanprover.github.io/lean4/doc/builtintypes.html)

### FBIP

Functional but in-place
是纯函数式语言在保持纯函数式的同时，为了高效表示状态的一种优化。同时，reuse
analysis 也降低了模式匹配等操作的开销。

[Perceus: Garbage Free Reference Counting with Reuse](https://www.microsoft.com/en-us/research/publication/perceus-garbage-free-reference-counting-with-reuse/)

[FP² : Fully in-Place Functional Programming](https://www.microsoft.com/en-us/research/publication/fp2-fully-in-place-functional-programming-2/)

### Glued Evaluation

### Compiling with Continuations

### Typeclass Organisation

### Algebra Tactics Optimisation

理论基础：[Reflexive Tactics for Algebra, Revisited](https://drops.dagstuhl.de/opus/volltexte/2022/16738/)

参考实现：[Algebra Tactics](https://github.com/math-comp/algebra-tactics)

## 实现细节的技术选择

### Variable

### Universe

### Proof Irrelevance
