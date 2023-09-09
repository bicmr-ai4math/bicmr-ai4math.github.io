# 常见的准备工作

请确保在知道每一条命令/每一个选项的意思都被完全理解后再进行这一步操作。

## 环境变量

`your_proxy_url` 的形式为

```
http://127.0.0.1:7890
^协议  |         |
       ^本地服务器地址
                 |
                 ^本地服务器端口
```

### 正在使用什么 shell？

请自行在互联网搜索以下的相关概念与图片进行判断。

设置代理不需要以下之外的任何环境变量。

#### POSIX 兼容

- Windows：MSYS2、Git Bash、WSL、…
- macOS、Linux：Zsh、Bash、…

```sh
export https_proxy=<replace_with_your_proxy_url> && export http_proxy=<replace_with_your_proxy_url>
```

#### CMD/PowerShell

如果正在使用 CMD，建议使用 PowerShell

- Windows

```PowerShell
Set https_proxy=<replace_with_your_proxy_url>
Set http_proxy=<replace_with_your_proxy_url>
```

### 在 VSCode 可以使用 Lean，但没法 `lake build` / `lake exe cache get`

检查

- Unix：`~/.elan/bin`
- Windows：用户文件夹下的 `.elan\bin`

是否在 `PATH`。

添加到 `PATH`：

- Unix：`echo $PATH`，`export PATH=$HOME/.elan/bin:$PATH`
- Windows：按下 Windows 键，输入「环境」进行搜索，配置对应选项中的 `PATH`

### 其他参见

- [Can I get "&&" or "-and" to work in PowerShell?](https://stackoverflow.com/questions/563600/can-i-get-or-and-to-work-in-powershell)

## 代理

### 如果成功让浏览器访问网页被代理，但是本地软件无法使用代理

找到代理服务商所提供的「订阅」，使用一个能解析订阅的本地代理服务器软件，如 Clash
Verge 或 Clash for Windows。请找到官方 GitHub 的 releases。

在启动软件后，找到对应的选项，查看自己的协议、地址、段口号。尽量使用 `http`
而不是 `socks5`。（如果你使用 `https` 作为协议（不出现在是变量名中的
`https_proxy`），请确保真的在使用 `https`
作为本地代理服务协议，大部分情况应该使用 `http`）

若无必要，不要开启本地代理服务器的 LAN。

### 如果成功让一些软件被代理，但无法使用 Elan/Lake/Lean 仍然无法使用代理

配置对应的 proxy 环境变量。可以使用 `curl` 测试环境变量是否妥当。

### 关闭终端重新打开后/在别的程序中 代理失效？

根据自己使用的 shell，搜索学习对应的 shell init
scripts（`bashrc`、`zshrc`、`$PSHOME\Profile.ps1`、…）的相关资料。

## 应该使用什么 toolchain 版本？

### 如果在使用 [mathlib4](https://github.com/leanprover-community/mathlib4) 作为依赖创建项目

- https://github.com/leanprover-community/mathlib4/blob/master/lean-toolchain

### 如果在阅读（可能包含完成习题）现有的项目，如 [Mathematics in Lean](https://github.com/leanprover-community/mathematics_in_lean)

- 不要运行 `lake update`

## 使用 [mathlib4](https://github.com/leanprover-community/mathlib4) 作为依赖创建项目

- 学习使用 `lake new`，`lake new --help`
- https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency

## 在 macOS 上使用 Nix 安装的 Elan

- https://github.com/alissa-tung/dot-darwin/blob/c9a4dc886918c56f330439fb1233629873939844/Makefile#L21
