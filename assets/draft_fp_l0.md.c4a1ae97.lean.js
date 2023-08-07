import{_ as s,v as a,b as n,R as l}from"./chunks/framework.db3115df.js";const e="/assets/rs.17f17407.png",p="/assets/parsec.88c31b1e.png",t="/assets/free.e658b495.png",m=JSON.parse('{"title":"Lean 函数式程序设计","description":"","frontmatter":{},"headers":[],"relativePath":"draft/fp/l0.md","filePath":"draft/fp/l0.md"}'),o={name:"draft/fp/l0.md"},i=l(`<h1 id="lean-函数式程序设计" tabindex="-1">Lean 函数式程序设计 <a class="header-anchor" href="#lean-函数式程序设计" aria-label="Permalink to &quot;Lean 函数式程序设计&quot;">​</a></h1><h2 id="动机" tabindex="-1">动机 <a class="header-anchor" href="#动机" aria-label="Permalink to &quot;动机&quot;">​</a></h2><ul><li>许多策略会被翻译成函数式程序设计的常见组分，学习函数式程序设计对读懂这些策略具体如何工作有帮助</li></ul><div class="language-Lean4"><button title="Copy Code" class="copy"></button><span class="lang">Lean4</span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#A6ACCD;">def id {A : Type _} (x : A) : A := x</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def id : {A : Type _} -&gt; (x : A) -&gt; A := fun x =&gt; x</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def id {A : Type _} (x : A) : A := by</span></span>
<span class="line"><span style="color:#A6ACCD;">  exact x</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def id : {A : Type _} -&gt; (x : A) -&gt; A := by</span></span>
<span class="line"><span style="color:#A6ACCD;">  intro _ x</span></span>
<span class="line"><span style="color:#A6ACCD;">  exact x</span></span></code></pre></div><ul><li>归纳地定义数据类型、递归地在数据类型上定义函数的能力，是程序设计和逻辑推理的自然基础；有良好的函数式定义组织能力在对定义的结构做归纳时会更简单</li></ul><div class="language-Lean4"><button title="Copy Code" class="copy"></button><span class="lang">Lean4</span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#A6ACCD;">import Mathlib.Init.Logic</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">inductive ℕ where</span></span>
<span class="line"><span style="color:#A6ACCD;">  | zero : ℕ</span></span>
<span class="line"><span style="color:#A6ACCD;">  | succ : ℕ -&gt; ℕ</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def add : ℕ -&gt; ℕ -&gt; ℕ</span></span>
<span class="line"><span style="color:#A6ACCD;">  | .zero  , n =&gt; n</span></span>
<span class="line"><span style="color:#A6ACCD;">  | .succ m, n =&gt; .succ $ add m n</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def add_identity (n : ℕ) : n = add n .zero :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  match n with</span></span>
<span class="line"><span style="color:#A6ACCD;">  | .zero   =&gt; rfl</span></span>
<span class="line"><span style="color:#A6ACCD;">  | .succ n =&gt; congr_arg ℕ.succ $ add_identity n</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def add_succ (m n : ℕ) : .succ (add m n) = add m (.succ n) :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  match m with</span></span>
<span class="line"><span style="color:#A6ACCD;">  | .zero   =&gt; rfl</span></span>
<span class="line"><span style="color:#A6ACCD;">  | .succ m =&gt; congr_arg ℕ.succ $ add_succ m n</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def add_comm (m n : ℕ) : add m n = add n m :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  match m with</span></span>
<span class="line"><span style="color:#A6ACCD;">  | .zero   =&gt; add_identity n</span></span>
<span class="line"><span style="color:#A6ACCD;">  | .succ m =&gt; Eq.trans</span></span>
<span class="line"><span style="color:#A6ACCD;">      (congr_arg ℕ.succ $ add_comm m n)</span></span>
<span class="line"><span style="color:#A6ACCD;">      (add_succ n m)</span></span></code></pre></div><ul><li>在 Lean 中编写 tactics 的语法和语义定义都依赖于良好的函数式程序设计基础，特别是要有能处理 monadic 代码的能力</li></ul><p><code>CoreM</code>、<code>MetaM</code>、<code>TermElabM</code>、<code>TacticM</code></p><ul><li>函数式程序设计本身很有趣，Lean 也对函数式程序设计有一定支持</li></ul><div class="language-Lean4"><button title="Copy Code" class="copy"></button><span class="lang">Lean4</span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#A6ACCD;">@[default_target]</span></span>
<span class="line"><span style="color:#A6ACCD;">lean_exe «hello» {</span></span>
<span class="line"><span style="color:#A6ACCD;">  root := \`Main</span></span>
<span class="line"><span style="color:#A6ACCD;">}</span></span></code></pre></div><ul><li>有的证明过程本质上和函数式程序设计是相同的</li></ul><p><a href="https://plfa.github.io/Properties/" target="_blank" rel="noreferrer"><em>Programming Language Foundations in Agda</em> Properties: Progress and Preservation</a> deriving an evaluator from a proof of progress</p><ul><li>Lean 缺少很多 functional pearl 定位的库</li></ul><p><img src="`+e+'" alt="Functional programming with bananas, lenses, envelopes and barbed wire"></p><p><img src="'+p+'" alt="Design patterns for parser combinators"></p><p><img src="'+t+`" alt="Data types à la carte"></p><h2 id="列表" tabindex="-1">列表 <a class="header-anchor" href="#列表" aria-label="Permalink to &quot;列表&quot;">​</a></h2><ul><li>归纳定义的列表</li></ul><div class="language-Lean4"><button title="Copy Code" class="copy"></button><span class="lang">Lean4</span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#A6ACCD;">inductive List (A : Type _) where</span></span>
<span class="line"><span style="color:#A6ACCD;">  | nil  : List A</span></span>
<span class="line"><span style="color:#A6ACCD;">  | cons : A -&gt; List A -&gt; List A</span></span></code></pre></div><ul><li>在列表上递归定义函数</li></ul><div class="language-Lean4"><button title="Copy Code" class="copy"></button><span class="lang">Lean4</span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#A6ACCD;">def map {A B : Type _} : (A -&gt; B) -&gt; (List A -&gt; List B) :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  fun f xs =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">    match xs with</span></span>
<span class="line"><span style="color:#A6ACCD;">    | []      =&gt; []</span></span>
<span class="line"><span style="color:#A6ACCD;">    | x :: xs =&gt; f x :: map f xs</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def filter {A : Type _} (f : A -&gt; Bool) : List A -&gt; List A</span></span>
<span class="line"><span style="color:#A6ACCD;">  | []      =&gt; []</span></span>
<span class="line"><span style="color:#A6ACCD;">  | x :: xs =&gt; if f x</span></span>
<span class="line"><span style="color:#A6ACCD;">      then x :: filter f xs</span></span>
<span class="line"><span style="color:#A6ACCD;">      else      filter f xs</span></span></code></pre></div><ul><li>recursive schemes</li></ul><div class="language-Lean4"><button title="Copy Code" class="copy"></button><span class="lang">Lean4</span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#A6ACCD;">def foldl {A B : Type _} : (B -&gt; A -&gt; B) -&gt; B -&gt; List A -&gt; B :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  fun f acc xs =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">    match xs with</span></span>
<span class="line"><span style="color:#A6ACCD;">    | []      =&gt; acc</span></span>
<span class="line"><span style="color:#A6ACCD;">    | x :: xs =&gt; foldl f (f acc x) xs</span></span></code></pre></div><p><a href="https://stackoverflow.com/a/26036320" target="_blank" rel="noreferrer">Every <code>foldl</code> is a <code>foldr</code>.</a></p><ul><li>list comprehension</li></ul><div class="language-"><button title="Copy Code" class="copy"></button><span class="lang"></span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#A6ACCD;">[ x ] = pure x</span></span>
<span class="line"><span style="color:#A6ACCD;">[ f x | x &lt;- xs ] = map (fun x =&gt; f x) xs</span></span>
<span class="line"><span style="color:#A6ACCD;">[ f x y | x &lt;- xs, y &lt;- ys ] = join [ [f x y | y &lt;- ys ] | x &lt;- xs ]</span></span>
<span class="line"><span style="color:#A6ACCD;">[ c | p ] = if p then [c] else []</span></span></code></pre></div><div class="language-"><button title="Copy Code" class="copy"></button><span class="lang"></span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#A6ACCD;">pure x = [ x ]</span></span>
<span class="line"><span style="color:#A6ACCD;">map f xs = [ f x | x &lt;- xs ]</span></span>
<span class="line"><span style="color:#A6ACCD;">join xss = [ x | xs &lt;- xss, x &lt;- xs ]</span></span></code></pre></div><h2 id="option" tabindex="-1"><code>Option</code> <a class="header-anchor" href="#option" aria-label="Permalink to &quot;\`Option\`&quot;">​</a></h2><ul><li>归纳定义的 <code>Option</code></li><li>在 <code>Option</code> 上递归定义函数</li><li>callback hell</li></ul><h2 id="monads" tabindex="-1">Monads <a class="header-anchor" href="#monads" aria-label="Permalink to &quot;Monads&quot;">​</a></h2><ul><li>do</li><li>comprehension</li></ul><div class="language-"><button title="Copy Code" class="copy"></button><span class="lang"></span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#A6ACCD;">xs &gt;&gt;= k = join (k &lt;$&gt; xs)</span></span>
<span class="line"><span style="color:#A6ACCD;">join xss = xss &gt;&gt;= id</span></span></code></pre></div><h2 id="io" tabindex="-1">IO <a class="header-anchor" href="#io" aria-label="Permalink to &quot;IO&quot;">​</a></h2><ul><li>main</li></ul><h2 id="monad-transformers" tabindex="-1">Monad Transformers <a class="header-anchor" href="#monad-transformers" aria-label="Permalink to &quot;Monad Transformers&quot;">​</a></h2><ul><li>State</li><li>Identity</li><li>StateT</li></ul><h2 id="intuitionistic-logic" tabindex="-1">Intuitionistic Logic <a class="header-anchor" href="#intuitionistic-logic" aria-label="Permalink to &quot;Intuitionistic Logic&quot;">​</a></h2><h2 id="further-reading" tabindex="-1">Further Reading <a class="header-anchor" href="#further-reading" aria-label="Permalink to &quot;Further Reading&quot;">​</a></h2><ul><li>more about monads</li><li>more about recursive schemes</li><li>lenses and other optics</li></ul>`,39),c=[i];function r(d,A,C,u,g,h){return a(),n("div",null,c)}const f=s(o,[["render",r]]);export{m as __pageData,f as default};
