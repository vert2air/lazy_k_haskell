# stat

ラムダ式の構成要素の統計情報を表示

## コマンド形式

stat {-e:<ラムダ式>|<ファイル名>}

## 説明

-eオプションで直接与えられるか、<ファイル名> で示されるファイルに格納された
ラムダ式に対して、構成要素の統計情報を表示する。

関数適用の深さは、二分木表現にした場合を基準にカウントする。
よって、xz(yz) は、深さ 2 となる。
```
     app
    /   \
  app    app
 /  \    /  \
x    z  y    z
```

* Max Depth     <br> ラムダ抽象と関数適用の両方をカウントして、最大の深さ。
  * Abst. Depth <br> ラムダ抽象のみをカウントして、最大の深さ。 
  * App. Depth  <br> 関数適用のみをカウントして、最大の深さ。
* Count:
  * Abst.       <br> ラムダ抽象の出現回数。
  * Index var.  <br> bindされた変数の出現回数。
  * I           <br> Lazy K の I (= \x.x) の出現回数。
  * K           <br> Lazy K の K (= \xy.x) の出現回数。
  * S           <br> Lazy K の S (= \xyz.xz(yz)) の出現回数。
  * iota        <br> Lazy K の Iota形式の i の出現回数。
  * Jot         <br> Lazy K の Jot の 0 と 1 の出現回数の合計。
    * 0         <br> Lazy K の Jot の 0 の出現回数。
    * 1         <br> Lazy K の Jot の 1 の出現回数。
  * Free Variables <br> 以降は、自由変数の統計情報。
    * index _1  <br> de Bruijn Index で示された自由変数の出現回数。
    * index _2  <br> de Bruijn Index 毎に表示。
    * named 'x' <br> 名前付きの自由変数の出現回数。
    * named 'y' <br> 名前毎に表示。
  * Input Promise (0 origin): <br> 以降は、入力promiseの統計情報。
    * index <0  <br> 入力の何バイト目を参照しているか。
    * index <2  <br> 何バイト目かは、0オリジンで指定する。
  * Church Number (0 origin): <br> 以降は、数値への変換時に使用すデータの統計情報。

## example

ラムダ式が書かれたファイルを指定。

```
$ cabal run stat -- lazy/prime_numbers.lazy
Max Depth     :         41
  Abst. Depth :          0
  App. Depth  :         41
Count:
  Abst.       :          0
  Index var.  :          0
  I           :         82
  K           :        217
  S           :        240
  iota        :          0
  Jot         :          0
    0         :          0
    1         :          0
  Free Variables:
  Input Promise (0 origin):
```

コマンドライン引数で、ラムダ式を直接指定。

```
$ cabal run stat -- -e '\ _1'
Max Depth     :          1
  Abst. Depth :          1
  App. Depth  :          0
Count:
  Abst.       :          1
  Index var.  :          1
  I           :          0
  K           :          0
  S           :          0
  iota        :          0
  Jot         :          0
    0         :          0
    1         :          0
  Free Variables:
  Input Promise (0 origin):
```

自由変数と入力プロミスを含むケース。

```
$ cabal run stat -- -e '\ab.by<0a_4(_3xy)'
Max Depth     :          7
  Abst. Depth :          2
  App. Depth  :          5
Count:
  Abst.       :          2
  Index var.  :          2
  I           :          0
  K           :          0
  S           :          0
  iota        :          0
  Jot         :          0
    0         :          0
    1         :          0
  Free Variables:
    index _1  :          1
    index _2  :          1
    named 'x' :          1
    named 'y' :          2
  Input Promise (0 origin):
    input <0  :          1
```
