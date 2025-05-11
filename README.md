# Lazy K interpreter and tools for lambda calculus written in Haskell

"Let them use AI if they have no Japanese!"

All files are written in UTF-8 code. Add Japanese fonts if necessary. I like Myrica M font.

というわけで、基本的に文書やコメントは、日本語で書きます。

Haskell でコーディングした、Lazy Kのインタプリタと、
ラムダ計算の為のツール群です。

## Install

Gitリポジトリを取得します。

```
$ git clone https://github.com/vert2air/lazy_k_haskell.git
```

## Build

ラムダ計算は遅いです。少しでも速く動作させるために、最適化オプションの使用を
お勧めします。

```
$ cabal build -O2
```

## 実行

各コマンドの説明は、`docs/*.md' に記載があります。

### Lazy Kインタプリタの実行

#### 入力が不要な Lazy K プログラムの実行例

素数を順に出力するプログラムです。 どんどん遅くなりますが、無限に出力するので、
適当なところで Ctrl-C 等で止めてください。

```
$ cabal run -O2 lazy -- lazy/prime_numbers.lazy
2 3 5 7 
```

指定文字数を出力した後に停止させる場合、--maxオプションが使えます。
この例だと、8文字出力後に停止します。1秒ぐらい掛かります。
ちなみに、11文字だと、29秒ぐらい掛かります。

```
$ cabal run -O2 lazy -- --max 8 lazy/prime_numbers.lazy
2 3 5 7 
```

-v オプションで、debug目的のログが、標準エラーに出力されます。

-d 1,20 オプションで、beta簡約の進捗状況を確認する目的の「\*」や「.」が、
標準エラーに出力されます。1 と 20 は、「\*」と「.」の出力頻度を指定します。

#### 入力が必要な Lazy K プログラムの実行例

入力の byte 列の生成は、echo を -ne オプション付きで使うと簡単です。
出力の byte 列の確認は、od -c -tx1 を使うと簡単です。

```
$ echo -ne '\x07\x30' | \
cabal run -O2 lazy -- lazy/add_A_B.lazy | \
od -c -tx1
0000000   7
         37
0000001
```

## Test

単体試験の実行です。

```
$ cabal test
```

doctestの実行です。

```
cabal repl --with-compiler=doctest
```

## License

lazy/ ディレクトリ配下の Lazy K プログラムは、
他のサイトからコピーしたものがあります。
コピー部分を含むテキストファイルは、冒頭に参照先の情報があります。
これらのファイルのライセンスは参照サイトのポリシーに従います。

このリポジトリに含まれる上記以外のファイルは、MIT ライセンスに従います。
