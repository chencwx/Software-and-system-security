# 恶意软件防御体系

## 实验原理（课堂笔记）

### 基本防御体系

+ 杀毒软件的原理，最核心的是对系统中的所有文件进行全盘的扫描，将每个文件的静态特征，主要是文件类型、文件的hash值得数据与一个数据库中保存的信息进行对比。这个数据库中，主要保存的是一些已经发现的蠕虫病毒、恶意软件的hash值等静态特征。如果能匹配上，说明扫描到的文件是一个蠕虫病毒或者恶意软件。那么就进行删除。
+ 由于会不停的有恶意软件、蠕虫病毒出现。所以，开发杀毒软件的厂家，必须还需要进行一个工作就是病毒数据库的更新。把厂家们已经发现的恶意软件加入到病毒数据库中，并让已经安装在客户主机中的杀毒软件定期链接服务器，升级病毒数据库。
+ 这个机制，简单、容易实现，所以杀毒软件很早就被开发出来了。在杀毒软件的基础上，人们还开发出了入侵检测系统。把数据库和对数据的扫描做成一个单独的设备，这个设备安装在一个网络的入口处，所有进入这个网络的数据流量都和恶意数据的特征库进行比较，找出其中可能有问题的数据并拦截。
+ 但是这种基于静态特征的匹配和查杀机制，很明显有缺陷。
  + 第一个缺陷，就是它的查杀是滞后的。杀毒软件能够查杀到的前提，是病毒的特征已经在数据库中。而这个数据库的特征是人为加入的。如果黑客们开发了一个新的蠕虫病毒或者什么攻击程序，杀毒软件是无法查杀的。只有当一个恶意软件已经流行开了，被杀毒软件厂家获得了样本，进行了逆向分析以后，才能确定其是否恶意，并提取其hash值等静态特征。
  + 二是从获得样本中进行软件的行为分析判断其是否恶意并不容易，需要有很多的逆向工程的工作。我们学过逆向工程的基本原理，知道这个工作需要有非常高的专业技能，同时有非常耗时间。三是恶意程序的源代码在黑客手里，他们要想进行变异，绕过杀毒软件的特征检测非常容易，只需略微进行修改，重新编译，hash就变了。
+ 几种改进方式。
  - 第一种，改进样本的获取渠道，原来杀毒软件厂家会在网络中容易被攻击的地方布置一些“陷阱”，如果恶意软件攻击进入了这些陷阱，杀毒软件厂家就获得了样本，这些陷阱就是早期的蜜罐。但是这种蜜罐只对蠕虫病毒等大规模流行的恶意软件有作用，对于一些定点的攻击很难获得样本。所以后来，有杀毒软件厂家基于黑白名单机制，开发了一种直接从用户主机和网络流量中获取大量样本的方法。把一些已知的可信的正常的软件加入到一个“白名单”中，就像发一个“良民证”一样，这些软件就不查了。对于已经在黑名单中的文件，全部无条件查杀。对于既不在白名单又不在黑名单中的新的样本，全部回传到服务器。这种改进方法，虽然解决了样本获取的问题，但是带来了新的问题，一是可能造成用户隐私泄露，造成用户的反感，甚至卸载防御软件，二是虽然解决了样本获取的问题，样本量却变得很大，是否能进行有效的分析变成了问题。
  - 第二种，改进思路，就是既然静态特征这么容易被绕过，那么有没有可能从软件行为上来分析，静态特征容易伪装，行为特征不容易伪装。黑客们再怎么修改源代码，他不可能把功能都修改了。比如蠕虫病毒，一定会去复制自己，把原有的良好程序修改后嵌入自己（比如熊猫烧香），或者进行网络的扫描，发现可利用的漏洞进入其他系统（比如冲击波病毒）。再比如，勒索软件一定会进行全盘加密、下载执行器一定会调用下载和执行相关的API。所以后来出现了一些分析软件行为特征的客户端防御软件，我们成为主机入侵防御（检测）系统。HIPS或者HIDS。但是这种第二种改进思路，又出现了新问题，要想分析行为，必须劫持软件的运行过程。比如采用我之前讲过的hook技术，记录软件调用的系统API。但是这种技术，会造成系统运行效率的低下，系统变得很慢很卡；同时还会造成不稳定。这种牺牲了用户系统的性能和稳定性的技术，虽然防御效果比纯静态特征要好得多（也不是十分完美，有一些高级的攻击还是防不住），但是用户却并不喜欢。代价太大。
  - 第三种改进思路，就是从源头上着手。蠕虫病毒也好、后门软件间谍程序、勒索软件，所有的有恶意软件，要想在目标系统中搞破坏，非法进入到目标系统，无非两条途径。一是利用漏洞，二是利用社工。其中漏洞是主要的途径，也是技术上可防御的途径。所以大家有纷纷开始加强堵漏洞。一是出现了漏洞数据库这样的东西，专门披露未知漏洞；二是大型的软件厂家，纷纷开发定期的漏洞补丁升级机制，最早最典型的就是微软。第三是加大软件发布前的安全测试工作。比如采用我们之前将的Fuzzing技术、符号执行技术，先进行自测。那么黑客发现新的位置漏洞的可能性就小一些。这种改进的效果比较好。发现的软件漏洞的数量越来越多，修补得越来越快，黑客发现新的未知漏洞的成本越来越高。这也形成了新的趋势，就是个人黑客越来越没有生存空间，蠕虫病毒等没有什么“经济价值”对攻击者没有什么回报的攻击越来越少。但是出现了勒索软件、APT攻击等新的方式，同时也意味着一旦被攻击，后果非常严重。
+ 今天我们的整体防御体系的架构，经过了多年发展，形成了这样的局面。
  - 第一，在客户端，轻量级的静态特征匹配为主杀毒软件并没有消失，还是广泛安装，操作系统自带了杀毒软件，比如Windows Defender等，国内360等装机量仍然非常巨大，但是他们都是轻量级的静态特征匹配为主。更重要的，在客户端，漏洞的补丁安装和管理更规范更及时，大多数用户由于各种惨痛经历，也积极打补丁。
  - 第二，形成了专业的位置样本分析系统，不在用户的客户端直接进行行为分析，而是由专业的系统进行样本的行为分析。这样，既能保证分析的准确性，又不影响用户主机的性能和稳定性。
+ 专业的网络安全公司，都是大型的软件分析沙箱系统，用于分析新出现的样本，判定其是否恶意，并向客户端及时发布样本特征。
+ 以上的整个防御机制。分三大块，一是最核心的漏洞管理；二是大型的自动化的程序分析、沙箱和蜜罐系统；三是主机端的静态特征查杀。这三者相互关联，高度配合。
+ 这个防御机制，虽然比一开始的杀毒要先进了不少，但是还是有防不住的情况。第一用户故意不打补丁、长期不升级软件等情况还是会形成漏洞。二是防不了社工，比如钓鱼和诈骗邮件等。比如给面试的考生发一个 "录屏软件.exe"这样的钓鱼攻击。诱骗用户主动运行。三是防御不了0day漏洞攻击。前两个，可能只能靠管理宣传和教育了。第三个，是安全研究人员研究的重点。
+ 围绕0day漏洞，也就是未知漏洞的挖掘和防御。攻击方和防御方，谁先挖出0day漏洞，谁就占有先手。
+ 0day漏洞的挖掘，我们之前也讲过一些了。主流的就是就是Fuzzing和符号执行。我讲了基本的原理。现在在安全研究界，围绕Fuzzing和符号执行玩出了很多新的花样，各种花式Fuzzing和符号执行，开发了若干的开源系统。但是万变不离其宗，基本原理是一样的。大家掌握了基本原理，以后有机会进入具体研究工作时，可以再学习。



### 在HIPS和沙箱中普遍采用的程序行为分析技术

- 剖析软件，大约可以分为几个层次。从高到底，有系统级、模块级、函数级、基本块级和指令级。
  - 什么是系统级呢？就是一个完整的软件。比如我们看Windows系统的任务管理器，就是一个有完整功能的软件系统的监视。
  - 一个完整的软件系统，通常是由若干模块组成的，通常会有一个主模块和若干其他功能模块。在Windows系统中，主模块是exe文件，其他功能模块是dll等文件。主模块通常是程序的入口。我们在Windows Sysinternals系列工具中的进程浏览器就可以看到模块级。
  - 模块内部的程序组织单元是函数。有内部函数和外部函数。外部函数是一个软件系统自己实现的函数，外部函数是调用的其他第三方软件的接口函数，也包括操作系统的API。
  - 函数内部当然就是控制流图和指令了。一个控制流图是执行是的若干分支，在控制流图种连续执行的一系列指令集合，中间没有分支的，就是基本块。
  - 最细的，不能再细分的，就是指令了。
- 这5个层次，都可以进行运行时的trace和分析。不难理解，层次越高，追踪所获得的信息就越少，但是trace的时间越短。我们记录一个系统中所有的进程的创建和退出，是非常容易的，几乎不会消耗系统的性能。但是如果我们记录到每一个指令的运行，那么我们的系统将在全局上有3-4个数量级的性能下降，也就是原来运行1秒钟的程序，需要一个小时左右的时间了。这肯定是不现实的。
- 如果分析得太粗，可能会漏掉信息，如果分析的太细，数量级太大，又不可行。所以首先需要选择合适的层次进行分析。
- 在现代的沙箱系统中。通常是多个层次结合的。
- 比如先有一个进程的白名单机制。白名单的进程，就不用分析了。比如notepad，calc等，大家都知道他们是系统自带的一些小应用程序，没有分析的必要，就不浪费时间和资源。
- 对于其他不清楚功能的分析对象，可以逐层深入。进过多年的研究，大家发现在函数这个层次的分析是效率上可行，而且所能获得信息比较有用的。有一种非常流行的技术，叫SSDT hook。
- SSDT既System Service Dispath Table。
- Windows系统中的系统调用也是一层一层的，比如之前给大家讲过的kernel32.dll提供了大部分系统管理相关的基础API，有几千个。经过分析发现，kernel32.dll还会调用一个ntdll.dll，这个dll这有几百个函数。ntdll.dll会从用户态进入系统内核态。当ntdll.dll进入到内核态时，就是通过SSDT来确定其所有调用的系统内核函数的地址。
- 从这个意义上来讲，SSDT相当于这个Windows系统内核的导出表。
- 数量在300个函数左右，根据不同的系统版本略有区别。而且这300个左右的函数，包括了所有重要的系统基础功能。大家发现这是一个非常好的监控程序行为的指标。
- 比如，其中打开和创建文件NtCreateFile函数，获取操作系统参数，NtQuerySystemInfomation，创建进程NtCreateProcess等等。如果监控了这个表，应用程序的大部分行为就都能获取了。
- 由此，衍生出一种非常重要的技术，基于系统调用序列的程序行为分析技术。把一个软件的系统调用序列和已知的恶意软件的系统调用序列进行分类。
- 比如把已知的恶意软件的系统调用序列让机器学习进行学习训练，然后再让新的未知样本的系统调用序列用训练好的引擎进行分类判定。这就是实现软件行为判定的一种自动化方法。
- 当然，有的时候，只是API这个层次还不够，可能还需要到控制流基本或者指令级别。那么如何去进行trace，获取程序执行内部的这些信息的。有几种技术
  + 首先，调试器是无所不能的。所有的程序执行细节都可以获得。而且高级的调试器是支持自动化的trace的，比如windbg和gdb都可以支持外挂脚本。
  + 第二，对于API层次，可以用我们熟悉的hook技术。
  + 第三，对于控制流和指令级别，除了可以用调试器以外，还可以用插装工具。插桩工具时一类专门用于程序trace的工具，其原理是通过在需要监控的程序点插入桩（记录程序运行的代码），来实现对程序运行过程的记录。最典型的插桩工具时 intel 公司的 pin tools,插桩工具的基本原理是在程序中插pin（桩），在程序运行到有pin位置，pin会调用一个分析者自行编写的回调函数，在回调函数内部完成记录分析或者安装新的桩等工作.
- 我们对疑似恶意软件的分析，要在一个隔离环境中进行。
- 对恶意软件进行隔离是因为，恶意软件有可能对去环境进行破坏，你肯定不想在你自己的工作主机上运行一个勒索软件吧。那怎么隔离呢？虚拟机。
- 所以安全研究人员们，开发了一种专门的既可以隔离恶意软件（使其恶意行为之限定在虚拟机内部，不会对其他环境造成而已的破坏）同时又可以追踪分析软件行为的的工具。就是沙箱。目前应用得最广泛的沙箱是 cuckoo。比较幸运的是它的编程接口是python的。使用cuckoo，你不用去过分深入的研究让人头痛的系统内核机制和指令集，在cuckoo的中就可方便的进行程序行为分析了。



## 课后实验

+ 安装并使用cuckoo，任意找一个程序，在cuckoo中trace获取软件行为的基本数据。

  + 实验环境：ubuntu16.04+windows7
  + 实验原理：cuckoo在部署阶段，在Guest系统里塞了一个agent，这个agent在运行阶段负责与Host端程序进行通信，从Host端接收sample, 整个客户端程序，以及配置文件。Cuckoo 的架构比较简单，在 Host 机上运行 Cuckoo 主程序，多个 Guest 机通过虚拟网络与 Host 机相连
  
+ 主机配置如下：
  
+ 安装`cuckoo`依赖
  
    ```bash
    sudo apt-get install git mongodb libffi-dev build-essential python-django python python-dev python-pip python-pil python-sqlalchemy python-bson python-dpkt python-jinja2 python-magic python-pymongo python-gridfs python-libvirt python-bottle python-pefile python-chardet tcpdump -y
  ```
  
  ![](./image/C1.png)
  
+ 安装Tcpdump并确认安装无误：
  
    ```bash
    $ sudo setcap cap_net_raw,cap_net_admin=eip /usr/sbin/tcpdump
    $ getcap /usr/sbin/tcpdump 
    /usr/sbin/tcpdump = cap_net_admin,cap_net_raw+eip
  ```
  
  ![](./image/c2.png)
  
+ 安装Pydeep：
  
    ```bash
    $ wget http://sourceforge.net/projects/ssdeep/files/ssdeep-2.13/ssdeep-2.13.tar.gz/download -O ssdeep-2.13.tar.gz
    $ tar -zxf ssdeep-2.13.tar.gz
    $ cd ssdeep-2.13
    $ ./configure
    $ make
    $ sudo make install
    
    #确认安装无误
    $ ssdeep -V
    Then proceed by installing pydeep:
    
    $ sudo pip install pydeep
    Validate that the package is installed:
    
    $ pip show pydeep
    ---
    Name: pydeep
    Version: 0.2
    Location: /usr/local/lib/python2.7/dist-packages
    Requires:
  ```
  
+ 安装Volatility：
  
    ```bash
    #先安装依赖
    $ sudo pip install openpyxl
    $ sudo pip install ujson
    $ sudo pip install pycrypto
    $ sudo pip install distorm3
    $ sudo pip install pytz 
    
    #然后安装volatility
    $ git clone https://github.com/volatilityfoundation/volatility.git
    $ cd volatility
    $ python setup.py build
    $ python setup.py install
    
    #确认安装无误
    $ python vol.py -h
    
    
  ```
  
+ 安装Cuckoo：
  
    ```bash
    #建议在virtualenv中安装（virtualenv就是用来为一个应用创建一套“隔离”的Python运行环境。）
    
  $ virtualenv venv
  $ . venv/bin/activate
  (venv)$ pip install -U pip setuptools
  (venv)$ pip install -U cuckoo
  ```
  
  ![](./image/koo.png)
  
+ 安装成功后进入如下界面

    ![](./image/su.png)

+ 检查是否生成CWD文件 ，文件路径： /home/username(你的用户名)/.cuckoo/agent/agent.py 如果username下没有出现.cuckoo文件，因为它是隐藏文件可以使用快捷键ctrl+H显示隐藏文件。

+ 客户机（win7）：安装python环境和PIL,Pillow等，关闭防火墙、自动更新等
  
  ![](./image/close.png)
  
  ![](./image/uodate.png)
  
+ 网络配置
  
+ 在virtualbox中添加一块网卡，管理——主机网络管理器，按照下面信息进行设置。
  
  ![](./image/host.png)
  
+ 设置windows 7网络，设置为Host-Only。界面名称为刚刚设置的网卡。
  
  ![](./image/in.png)
  
+ 进入Windows 7 系统，设置win7 ip网络
  
  ![](./image/7.png)
  
+ 检查是否配置成功，主机和客机是否能通信。

  主机中操作

    ```bash
    $ ping 192.168.56.101
    ```

  客机中操作

    ```bash
    $ ping 192.168.56.1
    ```


- 设置IP报文转发，这是在Ubuntu中的操作，因为win7无法上网，所以要通过主机才能访问网络，所以需要以下操作;
  流量转发服务：

  ```bash
  $ sudo vim /etc/sysctl.conf
  net.ipv4.ip_forward=1
  sudo sysctl -p /etc/systl.conf
  ```

  ![](./image/ip.png)
  
-  使用iptables提供NAT机制,注意：其中eth0为Ubuntu中的网卡名称，需要提前查看自己Ubuntu中的网卡名称然后修改eth0

   ```bash
   $ sudo iptables -A FORWARD -o eth0 -i vboxnet0 -s 192.168.56.0/24 -m conntrack --ctstate NEW -j ACCEPT
   $ sudo iptables -A FORWARD -m conntrack --ctstate ESTABLISHED,RELATED -j ACCEPT
   $ sudo iptables -A POSTROUTING -t nat -j MASQUERADE
   $ sudo vim /etc/network/interfaces
   # 新增下列兩行
   pre-up iptables-restore < /etc/iptables.rules #开机自启动规则
   post-down iptables-save > /etc/iptables.rules #保存规则
   sudo apt-get install iptables=persistent
   sudo netfilter-persistent save
   #dns
   $ sudo apt-get install -y dnsmasq
   $ sudo service dnsmasq start
   
   ```

+ 此时，win7已经能正常上网

+ 设置cuckoo配置文件

+ 配置virtualbox.conf

  ```bash
  $ vim virtualbox.conf
  machines = cuckoo1 # 指定VirtualBox中Geust OS的虛擬機名稱
  [cuckoo1] # 對應machines
  label = cuckoo1  .
  platform = windows
  ip = 192.168.56.101 # 指定VirtualBox中Geust OS的IP位置
  snapshot =snapshot
  #配置reporting.conf
  $ vim reporting.conf
  [jsondump]
  enabled = yes # no -> yes
  indent = 4
  calls = yes
  [singlefile]
  # Enable creation of report.html and/or report.pdf?
  enabled = yes # no -> yes
  # Enable creation of report.html?
  html = yes # no -> yes
  # Enable creation of report.pdf?
  pdf = yes # no -> yes
  [mongodb]
  enabled = yes # no -> yes
  host = 127.0.0.1
  port = 27017
  db = cuckoo
  store_memdump = yes 
  paginate = 100
  #配置cuckoo.conf
  version_check = no
  machinery = virtualbox
  memory_dump = yes
  [resultserver]
  ip = 192.168.56.1
  port = 2042
  ```

+ 启动cuckoo,进入venv中，输入命令启动cuckoo服务：

  ```bash
  cuckoo
  ```

+ 启动成功后，另外开出一个控制台，启动cuckoo web服务

  ```bash
  cuckoo web runserver
  ```

+ 启动成功后，会给出一个网站，用浏览器进行打开：

  ![](./image/cuckoo.png)

+ 接下来上传程序即可进行沙箱分析，提交样本可使用`cuckoo/utils/submit.py`,`cuckoo submit --url http://www.example.com`，下面是它的帮助信息

  ```bash
  usage: submit.py [-h] [-d] [--remote REMOTE] [--url] [--package PACKAGE]
                   [--custom CUSTOM] [--owner OWNER] [--timeout TIMEOUT]
                   [-o OPTIONS] [--priority PRIORITY] [--machine MACHINE]
                   [--platform PLATFORM] [--memory] [--enforce-timeout]
                   [--clock CLOCK] [--tags TAGS] [--baseline] [--max MAX]
                   [--pattern PATTERN] [--shuffle] [--unique] [--quiet]
                   [target]
  
  positional arguments:
    target                URL, path to the file or folder to analyze
  
  optional arguments:
    -h, --help            show this help message and exit
    -d, --debug           Enable debug logging
    --remote REMOTE       Specify IP:port to a Cuckoo API server to submit
                          remotely
    --url                 Specify whether the target is an URL
    --package PACKAGE     Specify an analysis package
    --custom CUSTOM       Specify any custom value
    --owner OWNER         Specify the task owner
    --timeout TIMEOUT     Specify an analysis timeout
    -o OPTIONS, --options OPTIONS
                          Specify options for the analysis package (e.g.
                          "name=value,name2=value2")
    --priority PRIORITY   Specify a priority for the analysis represented by an
                          integer
    --machine MACHINE     Specify the identifier of a machine you want to use
    --platform PLATFORM   Specify the operating system platform you want to use
                          (windows/darwin/linux)
    --memory              Enable to take a memory dump of the analysis machine
    --enforce-timeout     Enable to force the analysis to run for the full
                          timeout period
    --clock CLOCK         Set virtual machine clock
    --tags TAGS           Specify tags identifier of a machine you want to use
    --baseline            Run a baseline analysis
    --max MAX             Maximum samples to add in a row
    --pattern PATTERN     Pattern of files to submit
    --shuffle             Shuffle samples before submitting them
    --unique              Only submit new samples, ignore duplicates
    --quiet               Only print text on failure
  ```

+ 下面是我测试的一个程序的分析结果，暂时还看不太懂

  ![](./image/cce.png)

## 实验参考资料

+ [ssd hook](https://resources.infosecinstitute.com/hooking-system-service-dispatch-table-ssdt/#gref)
+ [SSDT-HOOK](https://github.com/xiaofen9/SSDTHOOK)
+ [HOOK](https://www.cnblogs.com/boyxiao/archive/2011/09/03/2164574.html)
+ [SSDT IN WINDOWS](https://ired.team/miscellaneous-reversing-forensics/windows-kernel/glimpse-into-ssdt-in-windows-x64-kernel)
+ [pin tools](https://software.intel.com/content/www/us/en/develop/articles/pin-a-dynamic-binary-instrumentation-tool.html)
+ [cuckoo](https://cuckoosandbox.org/)
+ [cuckoo教程](https://www.jianshu.com/p/f623fa0bebf9)
+ [cuckoo博客](https://blog.csdn.net/Bingoooooo_/article/details/94248229)
+ [cuckoo依赖](https://cuckoo.sh/docs/installation/host/requirements.html)