import{_ as a,v as e,b as l,R as s}from"./chunks/framework.3ac7bdc3.js";const b=JSON.parse('{"title":"常见的准备工作","description":"","frontmatter":{},"headers":[],"relativePath":"draft/misc/setup.md","filePath":"draft/misc/setup.md"}'),o={name:"draft/misc/setup.md"},t=s(`<h1 id="常见的准备工作" tabindex="-1">常见的准备工作 <a class="header-anchor" href="#常见的准备工作" aria-label="Permalink to &quot;常见的准备工作&quot;">​</a></h1><p>请确保在知道每一条命令/每一个选项的意思都被完全理解后再进行这一步操作。</p><h2 id="环境变量" tabindex="-1">环境变量 <a class="header-anchor" href="#环境变量" aria-label="Permalink to &quot;环境变量&quot;">​</a></h2><p><code>your_proxy_url</code> 的形式为</p><div class="language-"><button title="Copy Code" class="copy"></button><span class="lang"></span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#A6ACCD;">http://127.0.0.1:7890</span></span>
<span class="line"><span style="color:#A6ACCD;">^协议  |         |</span></span>
<span class="line"><span style="color:#A6ACCD;">       ^本地服务器地址</span></span>
<span class="line"><span style="color:#A6ACCD;">                 |</span></span>
<span class="line"><span style="color:#A6ACCD;">                 ^本地服务器端口</span></span></code></pre></div><h3 id="正在使用什么-shell" tabindex="-1">正在使用什么 shell？ <a class="header-anchor" href="#正在使用什么-shell" aria-label="Permalink to &quot;正在使用什么 shell？&quot;">​</a></h3><p>请自行在互联网搜索以下的相关概念与图片进行判断。</p><p>设置代理不需要以下之外的任何环境变量。</p><h4 id="posix-兼容" tabindex="-1">POSIX 兼容 <a class="header-anchor" href="#posix-兼容" aria-label="Permalink to &quot;POSIX 兼容&quot;">​</a></h4><ul><li>Windows：MSYS2、Git Bash、WSL、…</li><li>macOS、Linux：Zsh、Bash、…</li></ul><div class="language-sh"><button title="Copy Code" class="copy"></button><span class="lang">sh</span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#C792EA;">export</span><span style="color:#A6ACCD;"> https_proxy</span><span style="color:#89DDFF;">=&lt;</span><span style="color:#C3E88D;">replace_with_your_proxy_ur</span><span style="color:#A6ACCD;">l</span><span style="color:#89DDFF;">&gt;</span><span style="color:#A6ACCD;"> </span><span style="color:#89DDFF;">&amp;&amp;</span><span style="color:#A6ACCD;"> </span><span style="color:#C792EA;">export</span><span style="color:#A6ACCD;"> http_proxy</span><span style="color:#89DDFF;">=&lt;</span><span style="color:#C3E88D;">replace_with_your_proxy_ur</span><span style="color:#A6ACCD;">l</span><span style="color:#89DDFF;">&gt;</span></span></code></pre></div><h4 id="cmd-powershell" tabindex="-1">CMD/PowerShell <a class="header-anchor" href="#cmd-powershell" aria-label="Permalink to &quot;CMD/PowerShell&quot;">​</a></h4><p>如果正在使用 CMD，建议使用 PowerShell</p><ul><li>Windows</li></ul><div class="language-PowerShell"><button title="Copy Code" class="copy"></button><span class="lang">PowerShell</span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#A6ACCD;">Set https_proxy</span><span style="color:#89DDFF;">=&lt;</span><span style="color:#A6ACCD;">replace_with_your_proxy_url</span><span style="color:#89DDFF;">&gt;</span></span>
<span class="line"><span style="color:#A6ACCD;">Set http_proxy</span><span style="color:#89DDFF;">=&lt;</span><span style="color:#A6ACCD;">replace_with_your_proxy_url</span><span style="color:#89DDFF;">&gt;</span></span></code></pre></div><h3 id="在-vscode-可以使用-lean-但没法-lake-build-lake-exe-cache-get" tabindex="-1">在 VSCode 可以使用 Lean，但没法 <code>lake build</code> / <code>lake exe cache get</code> <a class="header-anchor" href="#在-vscode-可以使用-lean-但没法-lake-build-lake-exe-cache-get" aria-label="Permalink to &quot;在 VSCode 可以使用 Lean，但没法 \`lake build\` / \`lake exe cache get\`&quot;">​</a></h3><p>检查</p><ul><li>Unix：<code>~/.elan/bin</code></li><li>Windows：用户文件夹下的 <code>.elan\\bin</code></li></ul><p>是否在 <code>PATH</code>。</p><p>添加到 <code>PATH</code>：</p><ul><li>Unix：<code>echo $PATH</code>，<code>export PATH=$HOME/.elan/bin:$PATH</code></li><li>Windows：按下 Windows 键，输入「环境」进行搜索，配置对应选项中的 <code>PATH</code></li></ul><p>检查：</p><p>Unix</p><div class="language-sh"><button title="Copy Code" class="copy"></button><span class="lang">sh</span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#82AAFF;">which</span><span style="color:#A6ACCD;"> </span><span style="color:#C3E88D;">elan</span></span>
<span class="line"><span style="color:#82AAFF;">which</span><span style="color:#A6ACCD;"> </span><span style="color:#C3E88D;">lake</span></span>
<span class="line"><span style="color:#82AAFF;">which</span><span style="color:#A6ACCD;"> </span><span style="color:#C3E88D;">lean</span></span></code></pre></div><p>Windows</p><div class="language-PowerShell"><button title="Copy Code" class="copy"></button><span class="lang">PowerShell</span><pre class="shiki material-theme-palenight"><code><span class="line"><span style="color:#89DDFF;font-style:italic;">where</span><span style="color:#A6ACCD;"> elan</span></span>
<span class="line"><span style="color:#89DDFF;font-style:italic;">where</span><span style="color:#A6ACCD;"> lake</span></span>
<span class="line"><span style="color:#89DDFF;font-style:italic;">where</span><span style="color:#A6ACCD;"> lean</span></span></code></pre></div><h3 id="其他参见" tabindex="-1">其他参见 <a class="header-anchor" href="#其他参见" aria-label="Permalink to &quot;其他参见&quot;">​</a></h3><ul><li><a href="https://stackoverflow.com/questions/563600/can-i-get-or-and-to-work-in-powershell" target="_blank" rel="noreferrer">Can I get &quot;&amp;&amp;&quot; or &quot;-and&quot; to work in PowerShell?</a></li></ul><h2 id="代理" tabindex="-1">代理 <a class="header-anchor" href="#代理" aria-label="Permalink to &quot;代理&quot;">​</a></h2><h3 id="如果成功让浏览器访问网页被代理-但是本地软件无法使用代理" tabindex="-1">如果成功让浏览器访问网页被代理，但是本地软件无法使用代理 <a class="header-anchor" href="#如果成功让浏览器访问网页被代理-但是本地软件无法使用代理" aria-label="Permalink to &quot;如果成功让浏览器访问网页被代理，但是本地软件无法使用代理&quot;">​</a></h3><p>找到代理服务商所提供的「订阅」，使用一个能解析订阅的本地代理服务器软件，如 Clash Verge 或 Clash for Windows。请找到官方 GitHub 的 releases。</p><p>在启动软件后，找到对应的选项，查看自己的协议、地址、端口号。尽量使用 <code>http</code> 而不是 <code>socks5</code>。（如果你使用 <code>https</code> 作为协议（不出现在是变量名中的 <code>https_proxy</code>），请确保真的在使用 <code>https</code> 作为本地代理服务协议，大部分情况应该使用 <code>http</code>）</p><p>若无必要，不要开启本地代理服务器的 LAN。 在使用 WSL2 的某些版本时可能需要通过 <code>cat /etc/resolv.conf</code> 来获取代理服务器地址，此时需要开启本地代理服务器的 allow LAN/允许局域网连接选项。</p><h3 id="如果成功让一些软件被代理-但无法使用-elan-lake-lean-仍然无法使用代理" tabindex="-1">如果成功让一些软件被代理，但无法使用 Elan/Lake/Lean 仍然无法使用代理 <a class="header-anchor" href="#如果成功让一些软件被代理-但无法使用-elan-lake-lean-仍然无法使用代理" aria-label="Permalink to &quot;如果成功让一些软件被代理，但无法使用 Elan/Lake/Lean 仍然无法使用代理&quot;">​</a></h3><p>配置对应的 proxy 环境变量。可以使用 <code>curl</code> 测试环境变量是否妥当。</p><h3 id="关闭终端重新打开后-在别的程序中-代理失效" tabindex="-1">关闭终端重新打开后/在别的程序中 代理失效？ <a class="header-anchor" href="#关闭终端重新打开后-在别的程序中-代理失效" aria-label="Permalink to &quot;关闭终端重新打开后/在别的程序中 代理失效？&quot;">​</a></h3><p>根据自己使用的 shell，搜索学习对应的 shell init scripts（<code>bashrc</code>、<code>zshrc</code>、<code>$PSHOME\\Profile.ps1</code>、…）的相关资料。</p><h2 id="应该使用什么-toolchain-版本" tabindex="-1">应该使用什么 toolchain 版本？ <a class="header-anchor" href="#应该使用什么-toolchain-版本" aria-label="Permalink to &quot;应该使用什么 toolchain 版本？&quot;">​</a></h2><h3 id="如果在使用-mathlib4-作为依赖创建项目" tabindex="-1">如果在使用 <a href="https://github.com/leanprover-community/mathlib4" target="_blank" rel="noreferrer">mathlib4</a> 作为依赖创建项目 <a class="header-anchor" href="#如果在使用-mathlib4-作为依赖创建项目" aria-label="Permalink to &quot;如果在使用 [mathlib4](https://github.com/leanprover-community/mathlib4) 作为依赖创建项目&quot;">​</a></h3><ul><li><a href="https://github.com/leanprover-community/mathlib4/blob/master/lean-toolchain" target="_blank" rel="noreferrer">https://github.com/leanprover-community/mathlib4/blob/master/lean-toolchain</a></li></ul><h3 id="如果在阅读-可能包含完成习题-现有的项目-如-mathematics-in-lean" tabindex="-1">如果在阅读（可能包含完成习题）现有的项目，如 <a href="https://github.com/leanprover-community/mathematics_in_lean" target="_blank" rel="noreferrer">Mathematics in Lean</a> <a class="header-anchor" href="#如果在阅读-可能包含完成习题-现有的项目-如-mathematics-in-lean" aria-label="Permalink to &quot;如果在阅读（可能包含完成习题）现有的项目，如 [Mathematics in Lean](https://github.com/leanprover-community/mathematics_in_lean)&quot;">​</a></h3><ul><li>不要运行 <code>lake update</code></li></ul><h2 id="使用-mathlib4-作为依赖创建项目" tabindex="-1">使用 <a href="https://github.com/leanprover-community/mathlib4" target="_blank" rel="noreferrer">mathlib4</a> 作为依赖创建项目 <a class="header-anchor" href="#使用-mathlib4-作为依赖创建项目" aria-label="Permalink to &quot;使用 [mathlib4](https://github.com/leanprover-community/mathlib4) 作为依赖创建项目&quot;">​</a></h2><ul><li>学习使用 <code>lake new</code>，<code>lake new --help</code></li><li><a href="https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency" target="_blank" rel="noreferrer">https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency</a></li></ul><h2 id="在-macos-上使用-nix-安装的-elan" tabindex="-1">在 macOS 上使用 Nix 安装的 Elan <a class="header-anchor" href="#在-macos-上使用-nix-安装的-elan" aria-label="Permalink to &quot;在 macOS 上使用 Nix 安装的 Elan&quot;">​</a></h2><ul><li>缺失 <code>gmp</code> 库：<a href="https://github.com/alissa-tung/dot-darwin/blob/c9a4dc886918c56f330439fb1233629873939844/Makefile#L21" target="_blank" rel="noreferrer">https://github.com/alissa-tung/dot-darwin/blob/c9a4dc886918c56f330439fb1233629873939844/Makefile#L21</a></li></ul>`,46),n=[t];function r(c,i,p,h,d,u){return e(),l("div",null,n)}const y=a(o,[["render",r]]);export{b as __pageData,y as default};