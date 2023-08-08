import{_ as s,v as n,b as a,R as l}from"./chunks/framework.3ac7bdc3.js";const x=JSON.parse('{"title":"2023/08/08 revised","description":"","frontmatter":{},"headers":[],"relativePath":"draft/fp/l0/23-08-08.md","filePath":"draft/fp/l0/23-08-08.md"}'),p={name:"draft/fp/l0/23-08-08.md"},e=l(`<h1 id="_2023-08-08-revised" tabindex="-1">2023/08/08 revised <a class="header-anchor" href="#_2023-08-08-revised" aria-label="Permalink to &quot;2023/08/08 revised&quot;">​</a></h1><div class="language-Lean4"><button title="Copy Code" class="copy"></button><span class="lang">Lean4</span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#A6ACCD;">import Mathlib.Init.Logic</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">inductive ℕ where</span></span>
<span class="line"><span style="color:#A6ACCD;">  | zero : ℕ</span></span>
<span class="line"><span style="color:#A6ACCD;">  | succ : ℕ -&gt; ℕ</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def add : ℕ -&gt; ℕ -&gt; ℕ</span></span>
<span class="line"><span style="color:#A6ACCD;">  | .zero  , n =&gt; n</span></span>
<span class="line"><span style="color:#A6ACCD;">  | .succ m, n =&gt; .succ $ add m n</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">variable {A : Type _} {b : Type _}</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">@[simp] def foldl : (B -&gt; A -&gt; B) -&gt; B -&gt; List A -&gt; B :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  fun f acc xs =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">    match xs with</span></span>
<span class="line"><span style="color:#A6ACCD;">    | []      =&gt; acc</span></span>
<span class="line"><span style="color:#A6ACCD;">    | x :: xs =&gt; foldl f (f acc x) xs</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">-- foldl op acc []        = acc</span></span>
<span class="line"><span style="color:#A6ACCD;">-- foldl op acc (x :: xs) = foldl op (op acc x) xs</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">@[simp] def length : List A -&gt; ℕ :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  fun xs =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">    match xs with</span></span>
<span class="line"><span style="color:#A6ACCD;">    | []      =&gt; .zero</span></span>
<span class="line"><span style="color:#A6ACCD;">    | _ :: xs =&gt; .succ $ length xs</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">@[simp] def length&#39; : List A -&gt; ℕ :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  foldl (fun acc _ =&gt; .succ acc) .zero</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">example : let xs := [0, 1, 2, 3, 4]; length&#39; xs = length xs := by</span></span>
<span class="line"><span style="color:#A6ACCD;">  rfl</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def length&#39;_is_length (xs : List A) : length&#39; xs = length xs := by</span></span>
<span class="line"><span style="color:#A6ACCD;">  sorry</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">@[simp] def append : List A -&gt; List A -&gt; List A :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  fun xs ys =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">    match xs with</span></span>
<span class="line"><span style="color:#A6ACCD;">    | []      =&gt; ys</span></span>
<span class="line"><span style="color:#A6ACCD;">    | x :: xs =&gt; x :: append xs ys</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">-- def append :</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">example : append [0, 1, 2] [3, 4] = [0, 1, 2, 3, 4] :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  rfl</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def append_length (xs ys : List A) : add (length xs) (length ys) = length (append xs ys) :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  match xs with</span></span>
<span class="line"><span style="color:#A6ACCD;">  | []      =&gt; by</span></span>
<span class="line"><span style="color:#A6ACCD;">      simp</span></span>
<span class="line"><span style="color:#A6ACCD;">      rfl</span></span>
<span class="line"><span style="color:#A6ACCD;">  | x :: xs =&gt; by</span></span>
<span class="line"><span style="color:#A6ACCD;">      simp</span></span>
<span class="line"><span style="color:#A6ACCD;">      apply congr_arg ℕ.succ</span></span>
<span class="line"><span style="color:#A6ACCD;">      apply append_length</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def reverse : List A -&gt; List A :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  fun xs =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">    match xs with</span></span>
<span class="line"><span style="color:#A6ACCD;">    | []      =&gt; []</span></span>
<span class="line"><span style="color:#A6ACCD;">    | x :: xs =&gt; append (reverse xs) [x]</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">example : reverse [0, 1, 2, 3, 4, 5] = [5, 4, 3, 2, 1, 0] := by</span></span>
<span class="line"><span style="color:#A6ACCD;">  rfl</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def reverse&#39; : List A -&gt; List A :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  foldl (fun acc x =&gt; x :: acc) []</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">example : let xs := [0, 1, 2, 3, 4, 5]</span></span>
<span class="line"><span style="color:#A6ACCD;">  reverse&#39; xs = reverse xs := by</span></span>
<span class="line"><span style="color:#A6ACCD;">    rfl</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">---</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def pure&#39; : A -&gt; List A := (· :: [])</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def map : (A -&gt; B) -&gt; (List A -&gt; List B) :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  fun f xs =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">    match xs with</span></span>
<span class="line"><span style="color:#A6ACCD;">    | [] =&gt; []</span></span>
<span class="line"><span style="color:#A6ACCD;">    | x :: xs =&gt; f x :: map f xs</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">def join : List (List A) -&gt; List A :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  foldl (fun acc xs =&gt; append acc xs) []</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">example : join [[0], [1, 2, 3, 4], [5, 6, 7]] = [0, 1, 2, 3, 4, 5, 6, 7] := by</span></span>
<span class="line"><span style="color:#A6ACCD;">  rfl</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">-- HINT: use \`sum\` and \`map\`</span></span>
<span class="line"><span style="color:#A6ACCD;">def join_length : sorry := sorry</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">--- \`pure\`, \`map\`, \`join\` &lt;-&gt; comprehension</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">-- [42]</span></span>
<span class="line"><span style="color:#A6ACCD;">#eval (pure&#39; 42 : List Int)</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">-- [ x          | x &lt;- [0, 1, 2, 3, 4, 5] ]</span></span>
<span class="line"><span style="color:#A6ACCD;">-- [ fun x =&gt; x | x &lt;- [0, 1, 2, 3, 4, 5] ]</span></span>
<span class="line"><span style="color:#A6ACCD;">#eval map (fun x =&gt; x) [0, 1, 2, 3, 4, 5]</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">-- [ x               | x &lt;- [0, 1, 2, 3, 4, 5] ]</span></span>
<span class="line"><span style="color:#A6ACCD;">-- [ fun x =&gt; ⟨x, x⟩ | x &lt;- [0, 1, 2, 3, 4, 5] ]</span></span>
<span class="line"><span style="color:#A6ACCD;">#eval map (fun x =&gt; (⟨x, x⟩ : Int × Int)) [0, 1, 2, 3, 4, 5]</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">-- [ ⟨x, y⟩            | x &lt;- [0, 1, 2, 3, 4, 5], y &lt;- [0, 1, 2, 3, 4, 5] ]</span></span>
<span class="line"><span style="color:#A6ACCD;">-- [ fun x y =&gt; ⟨x, y⟩ | x &lt;- [0, 1, 2, 3, 4, 5], y &lt;- [0, 1, 2, 3, 4, 5] ]</span></span>
<span class="line"><span style="color:#A6ACCD;">-- [ fun x =&gt; fun y =&gt; ⟨x, y⟩ | x &lt;- [0, 1, 2, 3, 4, 5], y &lt;- [0, 1, 2, 3, 4, 5] ]</span></span>
<span class="line"><span style="color:#A6ACCD;">-- join [ fun x =&gt; [ fun y =&gt; ⟨x, y⟩ | y &lt;- [0, 1, 2, 3, 4, 5] ] | x &lt;- [0, 1, 2, 3, 4, 5] ]</span></span>
<span class="line"><span style="color:#A6ACCD;">#eval join $ map (fun x =&gt; (map ((fun y =&gt; ⟨x, y⟩) : Int -&gt; Int × Int) [0, 1, 2, 3, 4, 5])) [0, 1, 2, 3, 4, 5]</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">-- [ x | x &lt;- [0, 1, 2, 3] | x != 2 ]</span></span>
<span class="line"><span style="color:#A6ACCD;">-- HINT: [ c | p ] = if p then [c] else []</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">--- \`map\`, \`join\` &lt;-&gt; \`bind\`</span></span>
<span class="line"><span style="color:#A6ACCD;">-- bind xs k = join (map k xs)</span></span>
<span class="line"><span style="color:#A6ACCD;">-- join xss  = bind xss id</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">-- https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Option.20do.20notation.20regression.3F.html</span></span>
<span class="line"><span style="color:#A6ACCD;">instance : Monad List where</span></span>
<span class="line"><span style="color:#A6ACCD;">  pure := pure&#39;</span></span>
<span class="line"><span style="color:#A6ACCD;">  bind := fun xs k =&gt; join (map k xs)</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">-- [ ⟨x, y⟩ | x &lt;- [0, 1, 2, 3, 4, 5], y &lt;- [0, 1, 2, 3, 4, 5] ]</span></span>
<span class="line"><span style="color:#A6ACCD;">example : List (Int × Int) := do</span></span>
<span class="line"><span style="color:#A6ACCD;">  let x &lt;- [0, 1, 2, 3, 4, 5]</span></span>
<span class="line"><span style="color:#A6ACCD;">  let y &lt;- [0, 1, 2, 3, 4, 5]</span></span>
<span class="line"><span style="color:#A6ACCD;">  pure ⟨x, y⟩</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">-- alias \`· &gt;&gt;= ·\` \`bind\`</span></span>
<span class="line"><span style="color:#A6ACCD;">example : List (Int × Int) :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  [0, 1, 2, 3, 4, 5] &gt;&gt;= fun x =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">    [0, 1, 2, 3, 4, 5] &gt;&gt;= fun y =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">      pure ⟨x, y⟩</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">example : List (Int × Int) :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  bind [0, 1, 2, 3, 4, 5] (fun x =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">    bind [0, 1, 2, 3, 4, 5] (fun y =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">      pure ⟨x, y⟩))</span></span>
<span class="line"><span style="color:#A6ACCD;"></span></span>
<span class="line"><span style="color:#A6ACCD;">-- we can also use \`$\`</span></span>
<span class="line"><span style="color:#A6ACCD;">example : List (Int × Int) :=</span></span>
<span class="line"><span style="color:#A6ACCD;">  bind [0, 1, 2, 3, 4, 5] fun x =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">    bind [0, 1, 2, 3, 4, 5] fun y =&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">      pure ⟨x, y⟩</span></span></code></pre></div>`,2),c=[e];function o(t,A,C,i,r,y){return n(),a("div",null,c)}const g=s(p,[["render",o]]);export{x as __pageData,g as default};
