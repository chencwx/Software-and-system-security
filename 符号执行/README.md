# 符号执行

## 实验原理

+ 符号执行是一种程序分析技术，和模糊测试的思路不一样，模糊测试是把测试对象当做一个黑盒子，不深入理解内部原理。符号执行是白盒测试技术，是基于程序分析的。或者说是一种程序分析技术，需要解析程序的源码（或者至少是反汇编后的汇编代码）。

+ 符号执行作为一种能够系统性探索程序执行路径的程序分析技术，能有效解决模糊测试冗余测试用例过多和代码覆盖率低这两个问题

+ 符号执行的主要思想是以符号输入代替程序的实际输入，以符号值代替程序运行过程中的实际值，并以符号布尔表达式表示程序中的分支条件。这样，一条程序执行路径就包含了一系列的符号变量、表达式赋值以及约束条件等，程序中的各路径的信息能以符号的形式被完整记录和保存。我们把某条执行路径上的所有分支条件所组成的约束集（Constraint Set）称为路径约束或路径条件（PC, Path Constraint，Path Condition）。符号执行的主要目的是通过对路径约束的求解来判断此条路径的可达性（Feasibility），并能给出执行此条路径的实际测试输入。这个描述有点抽象，简单来说，符号执行的目的是覆盖程序执行的每一个分支。方法就是查看和收集程序执行过程中每一个分支条件的具体条件，把这些具体条件收集起来，变成一个数学的表达式，然后通过一些方法自动化的求解这些表达式，得到满足执行程序的路径的具体的输入的值。就可以覆盖特定的程序分支了。

+ 举个例子

  ![](./image/1.png)

+ 左边的是一段示例代码，一共13行，包括两个函数，一个main函数，一个foo函数。程序有两个输入，从外部读入的数据x和y。程序有两个输入，从外部读入的数据x和y。假设在第五行有一个bug。我们的目的是有一种自动化的方法来找出这个bug

+ 前面已经说了Fuzzing技术在某些特定情况下有可能极其小得概率才能覆盖到特定分支，所以Fuzzing技术最大的问题就是代码覆盖率不高。对于穷尽每个执行路径目标来说有点难。那么符号执行在解析代码的情况下，首先把程序的每一个分支画出来。形成一个称为符号执行树的数据结构。这个符号执行树，和程序的控制流图有点类似。但是它要明确每个分支的具体的执行路径条件。

+ 比如第一个分支的执行条件是y>x,第二个分支的执行条件是y<z+10,x和y都是输入数据，在数学上来说，都是未知数。如果我们能够有一种方法，可以求解y>x的一个满足解和一个不满足解。那么是不是就找到了覆盖两个分支的两个测试用例。同样，对第二分支来说，在满足y>x的情况下，同时再满足y<z+10或者不满足 y<z+10，就能得到两个二级分支的具体的输入数据。这里多了一个变量z，通过分析代码发现，z并不是一个新的数据数据，所以他并不是未知数，而是其他未知数赋值而来，所以每一个步，我们都记录下这种赋值关系，形成一个“表达式组”，或者，说得简单点，我们初中的时候学的“不等式组”。

+ 理论上来讲，每一个程序执行的分支，每一个“执行路径”都有一个确定的不等式组作为执行条件。我们称为“约束”。如果能求解到这个不等式组的一个解，那么就可以构造出专门覆盖这条路径的测试数据了。我们称为“约束求解”

+ 这里，对于我们想要找的那个bug，第五行的代码。最终形成一个这样的“约束条件”

  ![](./image/2.png)

+ 下面的问题就是如何求解这个约束。我们的目的当时是自动化求解，不是人工求解。而且我们的目的是得到一个满足解即可，不用得到解析解。也就是只需要得到一个满足这个不等式组的具体的值，就等达到目的。

+ 如果我们把每一个路径的约束全部求解一遍，那么我们就能得到100%代码覆盖率的测试数据集。能够充分测试一个软件，找出软件中所有潜在的bug和漏洞。

+ 符号执行技术在上个世纪70年代被提出之后，受限于当时计算机的计算能力和约束求解技术的不足，并没有取得太大的进展。近年来，由于可满足模理论(SMT)研究以及动态符号执行技术的提出和应用使得符号执行技术研究有了革命性的进展，并已经被学术界和业界广泛应用于软件测试、漏洞挖掘、模型验证等领域。但是我们一直找不到一种自动化求解约束表达式的方法，所以也停留在理论层面。但是最近十几二十年情况不一样了。

+ 我们有了一种新的方法，并且开发出了工具，可以做到了。抽象一点，布尔可满足性问题（SAT，Boolean Satisfiability Problem），又称为命题可满足性问题（Propositional Satisfiability Problem），通常缩写为SATISFIABILITY或者SAT。布尔可满足性问题主要作用是在使用某种特定的语言描述对象（变量）的约束条件时，求解出能够满足所有约束条件的每个变量的值。SAT求解器已经被用于解决模型检查、形式化验证和其它包括成千上万变量和约束条件的复杂问题。但SAT问题是个NP完全问题，具有比较高的复杂度，且直接使用SAT求解器对程序进行分析的话需要需将问题转化为CNF形式的布尔公式，这给转化工作带来很大的困难。

+ 学过算法复杂度的同学知道，数学家已经证明了所有的NPC问题，都可以转化为SAT问题，后来发现一种算法，可以缓解这个问题，并在一定程度上求解。具体算法我们不用去深入了解，因为前人已经开发出工具了，简而言之是一种基于多维空间收敛搜索的方法。这个工具呢，我们称为 SAT 求解器。或者他的变种SMT 求解器。

+ 可满足模理论(SMT，Satisfiability Modulo Theories)主要用于自动化推论（演绎），学习方法，为了检查对于一些逻辑理论T的一阶公式的可满足性而提出的。SMT技术主要用于支持可推论的软件验证，在计算机科学领域已经被广泛应用于模型检测（Model Checking），自动化测试生成等。可以被用于检查基于一种或多种理论的逻辑公式的可满足性问题。典型的应用理论主要包括了各种形式的算术运算（Formalizations of Various Forms of Arithmetic），数组（Arrays），有限集（Finite Sets），比特向量（Bit Vectors），代数数据类型（Algebraic Datatypes），字符串（Strings），浮点数（Floating Point Numbers），以及各种理论的结合等。
  相对于SAT求解器，而言SMT求解器不仅仅支持布尔运算符，而且在使用SMT求解器的解决问题的时候不需要把问题转化成复杂的CNF范式，这使得问题得以简化。

+ 不过说白了就是一个结论，上面我们总结出来的“约束求解”问题有自动化的方法了，而且已经有人开发了工具了。

  ![](./image/3.png)

+ 其中比较优秀的是Z3，微软研究院开发的。

+ 来看[具体例子](https://rise4fun.com/z3)，约束求解器是怎么用到。

+ 打开网页以后，先看到左上。

  ![](./image/4.png)

+ 这个是SMT 求解器使用的一种描述语言。来描述变量之间的约束关系。

+ 我们来简化一下。

  ![](./image/5.png)

  ```c
  ; This example illustrates basic arithmetic and 
  ; uninterpreted functions
  
  (declare-fun x () Int)
  (declare-fun y () Int)
  (declare-fun z () Int)
  (assert (>= (* 2 x) (+ y z)))
  (assert (= x y))
  (check-sat)
  (get-model)
  (exit)
  ```

+ 这个formula呢，按照工具的要求语法，写成一种固定的形式。一二行是注释，3、4、5三行相当于定义了三个变量。这三个变量都是Int型的。7、8两行就是定义了两个约束。运算符写在前面，运算数写在后面。第一个约束表达式实际是。2*x >= y+z 9 10 11行是要求求解器做三个具体的事情。第一个是检测是否这个表达式是否满足。也就是有解还是没有解。当然会有没有解的表达式组的。例如 x>y and x<y 不管xy怎么取值，都没有解。就是一个不满足的情况。

+ 那么我们这个例子中，工具给出的结果是满足 sat。然后是要 get-model，其实就是得到解。一个具体的满足解。然后求解器给出了x=0 y=0 z=0就能满足两个约束。11行就简单了，告诉求解器，工作做完了可以退出。有了这个工具，之前图里的那个例子就能自动化了。

+ SMT-LIB（The satisfiability modulo theories library）自从2003年开始发起的为SMT理论研究提供标准化支持的项目，旨在促进SMT理论的研究和开发。SMT-LIB的目的主要如下：为SMT系统提供标准化严谨的背景理论描述；发展和促进SMT求解器的输入和输出语言；为SMT求解器研究团队建立和提供大型测试集library等。
  定义 如果对于用户声明(declare)的常量和函数，存在一个解（interpretation0能使全局栈里面的所有的公式集（the set of formulas）为true，则我们称这些公式集是可满足（satisfiable）的。

+ 再举个例子

  ![](./image/6.png)

+ 这个为SMT-LIB V2语言在实际约束求解中的应用。其中declare-fun 命令用于声明一个函数，当函数里面参数为空时，表示声明一个符号常量；assert命令用于添加一个约束式formula到SMT全局栈里面；check-sat 命令决定在栈里面的公式（formulas)是否是可满足的，如果是，则返回sat，如果不满足（not satisfiable，即unsatisfiable)，则返回unsat，如果求解器无法根据已有的formula决定是否满足，则返回unknown；get-value命令用于在check-sat命令返回的结果是sat的前提下获取满足使SMT求解器全局栈中所有formulas为true的其中的一个解。当前很多非常著名的软件测试工具都采用了符号执行技术，而且已经有很大一部分开放了源代码。例如：NASA的Symbolic (Java) PathFinder，伊利诺大学香槟分校（UIUC）的 CUTE和jCUTE，斯坦福大学（Stanford）的 KLEE, 加利福尼亚大学伯克利分校（UC Berkeley）的 CREST和 BitBlaze，瑞士洛桑联邦理工学院（EPEL）的S2E，卡内基梅隆大学（CMU）的Mayhem和Mergepoint，加利福尼亚大学圣巴巴拉分校（UC Santa Barbara）的angr等。
  在工业领域也有符号执行工具被广泛使用，如Microsoft(Pex, SAGE, YOGI和PREfix), IBM (Apollo), NASA 和Fujitsu的 (Symbolic PathFinder)等。可以看出来，符号执行确实是计算机领域一个非常重要的研究点。很多著名大学都在研究这个东西。

+ 上面说了这么多符号执行工具，这些工具是把我们刚才说的整个过程都实现了：根据代码生成符号执行树->收集路径的约束->转为SMT-LIB格式->输入给约束求解器->验证路径可达或者不可达，可达的情况下获得解->根据解自动构造输入数据,但是不同的符号执行工具在实现时有不同比如KLEE，只能分析C源码程序。后续的一些工具可以分析二进制程序。

+ KLEE是开源的，而且比较成熟[文档](https://klee.github.io/)比较多，我们来学习一下。

+ KLEE能实现全自动化，唯一的缺点是需要在程序中进行少量的修改。这个 klee_make_symbolic(&a, sizeof(a), "a");的作用就是a标记为需要求解的输入数据。

  ![](./image/7.png)

+  BitBlaze还有一些后续工具，能够实现输入数据的自动识别，更高级一些。使用KLEE一共就几个步骤：准备一份源码，标记要分析的输入数据，编译，使用KLEE来运行编译后的程序，得到KLEE自动生成的测试用例。最后把所有输入测试用例循环输入给被测试程序，完成自动测试。

+ 按照[官方的教程](https://klee.github.io/tutorials/testing-function/)，做一遍，比较简单,环境是Linux

+ [自动走迷宫](https://github.com/grese/klee-maze)

+ 符号执行的主要问题。

  + 当程序中有循环的时候，按照符号执行树，每一个分支条件都是需要展开。这会造成程序的路径非常多。循环是程序的一个基本结构，普遍存在的。这种情况要遍历每一个路径，实际路径数量会非常巨大。造成消耗的时间不可行。这个问题称为路径爆炸，路径的数据量是分支数量的指数级。循环更加强了这个问题。还有当程序路径非常多，输入变量非常多的时候，会超过SMT求解的求解能力。所以对大型程序，目前符号执行只是一种辅助性的手段。但是这种技术是有前景的，随着计算能力的增强，算法的优化和改进，未来可能成为程序分析、程序自动化测试和程序安全性分析的主要的形式化的方法。

+ 最后补充一点，KLEE当然不是使用的在线版本的示例性质的约束求解器。而是直接调用本地的二进制程序。Windows和Linux下都有Z3的可执行程序，Windows系统中是z3.exe，可以在官网下载。



## 课后实验

+ 作业：安装KLEE，完成官方tutorials。至少完成前三个，有时间的同学可以完成全部一共7个

  + 实验环境：virtualbox+ubuntu16.04 server

  + 安装依赖包

    ```bash
     $ sudo apt-get install build-essential curl libcap-dev git cmake libncurses5-dev python-minimal python-pip unzip
    ```

  + 安装LLVM 需要注意：对于不同版本的ubuntu应该到 [LLVM Package Repository](http://llvm.org/apt/) 找到对应版本的。写入source.list 中。

    ```bash
    
    deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial-3.9 main
     
    deb-src http://apt.llvm.org/xenial/ llvm-toolchain-xenial-3.9 main
    ```

    ![](./image/e1.png)

  + 添加repository key并下载llvm 3.9的packages

    ```bash
    
    $ wget -O - http://llvm.org/apt/llvm-snapshot.gpg.key|sudo apt-key add -  
     
    $ sudo apt-get update  
     
    $ sudo apt-get install clang-3.9 lldb-3.9
    ```

    ![](./image/e2.png)

    ![](./image/e3.png)

  + 需要在~/.bashrc里面改一下PATH：（注意不要在命令行中配置，否则每次开机都得配置一遍）

    ```bash
    export PATH="/usr/lib/llvm-3.9/bin:$PATH"
    ```

  + 安装约束解释器：选择的是STP，根据官网中的文档直接配置即可。可选项暂时未配置

  + 安装klee

    ```bash
    
    $ git clone https://github.com/jirislaby/klee.git
     
    $ cd klee
     
    $ git branch -a
     
    git checkout remotes/origin/better-paths
    ```

  + 配置KLEE

    ```bash
    
    $ mkdir klee_build_dir
     
    $ cd klee_build_dir
     
    $ cmake -DENABLE_SOlVER_STP=ON -DENABLE_SYSTEM_TESTS=OFF -DENABLE_UNIT_TESTS=ON ../klee
    ```

    ![](./image/e4.png)

  + 由于未配置可选项所以要将这些关闭。在cmake的过程中，会提示关闭。提示找不到Doxygen，则需要安装

    ```bash
     sudo apt-get install doxygen
    ```

  + 编译安装klee

    ```bash
    $ sudo make install
    ```

  + 若出现找不到liblibLLVM-3.9.so.so的情况，参考：http://terenceli.github.io/%E6%8A%80%E6%9C%AF/2017/06/08/klee-newbie

    ```
    make[2]: *** No rule to make target '/usr/lib/llvm-3.9/lib/liblibLLVM-3.9.so.so', needed by 'bin/gen-random-bout'.
    ```

  + 则利用软链接。

    ```bash
    $ ln -L libLLVM-3.9.so liblibLLVM-3.9.so.so
    ```

  + 官方 tutorial:（新建了一个klee用户便于实验，且环境是新搭建的）
  
  + 这个实例完整程序如下，在 `examples/get_sign 目录下，`用来判断一个整数的正，负，或者为0.
  
    ```c
    
    #include <klee/klee.h>
     
    int get_sign(int x) {
      if (x == 0)
         return 0;
      
      if (x < 0)
         return -1;
      else 
         return 1;
    } 
     
    int main() {
      int a;
      klee_make_symbolic(&a, sizeof(a), "a");
      return get_sign(a);
    }
    
    ```
  
  + 其中，klee_make_sybolic是KLEE自带的函数，用来产生符号化的输入。因为KLEE是在LLVM字节码上进行工作，所以我们首先需要将.c编译为LLVM字节码。首先，我们进入到该文件目录（~/klee_src/examples/get_sign）下执行命令
  
    ```bash
    clang -I ../../include -emit-llvm -c -g -O0 -Xclang -disable-O0-optnone get_sign.c
    ```
  
  + 其中，参数-I是为了编译器找到头文件klee/klee.h,-g是为了在字节码文件中添加debug信息，还有后面的，具体不深究，按照官网推荐来。同目录下我们会生成一个get-sign.bc的字节码文件，然后进行测试：
  
    ```bash
    $ klee get_sign.bc
    ```

    ![](./image/k1.png)
    
  + 可以看到结果中KLEE给出了总指令数，完整路径和生成的测试案例数。
  
  + 最后，我们看当前目录下多生成了两个文件：**klee-last** 和 **klee-out-0。**其中klee-out-0是本次测试结果，klee-last是最新测试结果，每次测试后覆盖。
  
    ![](./image/k2.png)
  
  + 符号化输入,为了利用KLEE测试这个函数，首先需要设置符号化输入，也就是把输入变量符号化。这里用到 klee_make_symbolic() 函数，该函数输入三个参数，分别是变量地址、变量大小、变量名（这个名可以自己随便取，就是用作标识）。之后设置一个main函数，调用klee-make-symbolic函数，再利用符号化的输入变量调用所要测试的函数get_sign。具体main函数的定义如下：
  
    ```c
    int main() {
      int a;
      klee_make_symbolic(&a, sizeof(a), "a");
      return get_sign(a);
    }
    ```
  
  + 编译程序生成LLVM bitcode,KLEE的分析是基于LLVM bitcode的，所以首先需要用llvm-gcc编译c文件生成文件，命令如下：
  
    ```bash
    $ llvm-gcc --emit-llvm -c -g get_sign.c
    ```
  
  + 生成get_sign.o文件，-g参数用于在编译中加入debug信息，以便于产生源代码级别的程序信息。同时编译中不要使用优化设置的参数。
  
  + 运行KLEE分析程序
  
    ```bash
     $ klee get_sign.o
    ```
  
  + 可以得到如下的输出：
  
    ```bash
    KLEE: output directory = "klee-out-0"
    
        KLEE: done: total instructions = 51
        KLEE: done: completed paths = 3
        KLEE: done: generated tests = 3
    ```
  
  +  从中可以看出，该测试函数有3条路径，并且为每一条路径都生成了一个测试例。KLEE执行输出信息都在文件klee-out-N中，不过最近一次的执行生成的目录由klee-last快捷方式指向。查看生成的文件：
  
    ```bash
    $ ls klee-last/
        assembly.ll      run.istats       test000002.ktest
        info             run.stats        test000003.ktest
        messages.txt     test000001.ktest warnings.txt
    ```
  
  + KLEE生成的测试例查看,扩展名为.ktest的都是生成的测试例，这个程序有三条path，所以三个测试例，这些文件都是二进制代码，可以用ktest-tool命令查看，具体如下：
  
    ```bash
    $ ktest-tool --write-ints klee-last/test000001.ktest
        ktest file : 'klee-last/test000001.ktest'
        args       : ['get_sign.o']
        num objects: 1
        object    0: name: 'a'
        object    0: size: 4
        object    0: data: 1
    
        $ ktest-tool --write-ints klee-last/test000002.ktest 
        ...
        object    0: data: -2147483648
    
        $ ktest-tool --write-ints klee-last/test000003.ktest
        ...
        object    0: data: 0
    ```
  
  +  很明显的可以看到，每一个路径对应的输入变量值，分别是1,  -2147483648, 0。
  
  + 利用测试例运行程序, 用生成的测试例作为输入运行程序，命令及结果如下：
  
    ```bash
     $ export LD_LIBRARY_PATH=path-to-klee-root/Release+Asserts/lib/:$LD_LIBRARY_PATH
    
            #LD_LIBRARY_PATH中的path-to-klee-root需要用具体的路径代替，后面的也一样
        $ gcc -L path-to-klee-root/Release+Asserts/lib/ get_sign.c -lkleeRuntest
    
            #gcc编译生成a.out，一个可执行程序，然后用下面的方式指定其输入为test000001.ktest。
    
        $ KTEST_FILE=klee-last/test000001.ktest ./a.out
        $ echo $?
    
            #查看返回值
        1
        $ KTEST_FILE=klee-last/test000002.ktest ./a.out
        $ echo $?
    
            #255实际上对应的是-1
        255
        $ KTEST_FILE=klee-last/test000003.ktest ./a.out
        $ echo $?
        0
    ```
  
    

## 实验参考资料

+ [klee安装](https://blog.csdn.net/goto2091/article/details/86602063)
+ [编译klee](https://blog.csdn.net/melissa_cjt/article/details/74995527)
+ [apt-get出错](https://blog.csdn.net/zyxlinux888/article/details/6358615)
+ [klee教程](https://blog.csdn.net/qq_26736193/article/details/103455451)