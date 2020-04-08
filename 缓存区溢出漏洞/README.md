# 缓冲区溢出漏洞底层

## 实验目的

+ 理解缓冲区溢出漏洞底层原理

## 实验步骤

### 原理

+ 先观察下面的代码

  ```c
  int main() 
  {
   char* a = malloc(100);
   a[101] = 'a';
  }
  ```

+ 我们分配了100个字节的内存单位。但是，这段代码，在执行的时候。不会有异常情况。原因在于，操作系统对内存的管理，也是有开销的。系统本身需要在一块单独的系统内存中记录那些内存是可用的，那些内存是不可用的。如果记录内存是否可用这个信息太细，那么记录所有的内存开销就很高。比如，如果我们记录详细到每一个bit是否可用。如果系统的内存有1GB，记录内存是否可用的内存也需要1GB。这个开销有点太大了。所以，实际上，没有记录到这么细。

+ 在Windows系统中，通常是以4KB为单位进行管理的。也就是要么这4KB，都可用，要么都不可用。这样，所需要的管理数据就小得多。所以，malloc还不是最底层的内存管理方式。malloc我们称为堆内存管理。malloc可以分配任意大小的数据，但是，malloc并不管理一块数据是否有效的问题。而是由更底层的虚拟内存管理来进行的。

+ 一个4MB的内存管理单元，我们称为一个内存分页。当malloc在内存分配时，如果已经可用的分页中，还有剩余的空间足够用，那么malloc就在这个可用的分页中拿出需要的内存空间，返回地址。如果已经可用的分页不够用，再去分配新的分页。然后返回可用的地址。所以，malloc分配可以比较灵活，但是系统内部，不会把内存搞得特别细碎。都是分块的。

+ 打开任务管理器，查看详细信息，发现全是4KB倍数

  ![](./image/4.png)

+ 这两个小实验，证明了，系统确实以4KB作为单元在管理内存，要么4KB全部有效，要么全部无效。上述实验虽然我们只分配了100个字节。但是这100个字节所在的整个4KB的内存全部是可用的。然后，我们每个4KB的内存分页，其实有三个属性，可读可写可执行，所以，我们甚至可以分配一块readonly的内存。

+ 那么如何改变一块内存的访问属性呢？用VirtualProtect 函数。虚拟内管管理，系统也提供了一些的函数来让应用程序可以自己管理。

+ 分配内存是用 VirtualAlloc，释放使用VirtualFree，修改属性使用 VirtualProtec大家记住这三个函数。只要是VirtualAlloc分配的内存，就可以使用。VirtualAlloc甚至可以指定希望将内存分配在哪个地址上。malloc函数底层也会调用VirtualAlloc函数。当没有足够的整页的的内存可用时，malloc会调用VirtualAlloc，所以，实际的内存分配，没有那么频繁。

## 实验

+ 阅读VirtualAlloc、VirtualFree、VirtualProtect等函数的官方文档。
+ 编程使用malloc分配一段内存，测试是否这段内存所在的整个4KB都可以写入读取。
+ 使用VirtualAlloc分配一段，可读可写的内存，写入内存，然后将这段内存改为只读，再读数据和写数据，看是否会有异常情况。然后VirtualFree这段内存，再测试对这段内存的读写释放正常。



## 实验参考资料

+ [虚拟内存管理](https://docs.microsoft.com/en-us/windows/win32/api/memoryapi/nf-memoryapi-virtualalloc)
+ [系统保护](https://docs.microsoft.com/zh-cn/windows/win32/memory/memory-protection-constants)
+ [virtual protect](https://docs.microsoft.com/en-us/windows/win32/api/memoryapi/nf-memoryapi-virtualprotect)
+ [virtual free](https://docs.microsoft.com/en-us/windows/win32/api/memoryapi/nf-memoryapi-virtualfree)
+ [virtual alloc](https://docs.microsoft.com/en-us/windows/win32/api/memoryapi/nf-memoryapi-virtualalloc)

