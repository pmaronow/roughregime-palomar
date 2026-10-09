#define _GNU_SOURCE
#include <unistd.h>
#include <dlfcn.h>
#include <string.h>
#include <ctype.h>
ssize_t readlink(const char *path, char *buf, size_t bufsiz) {
 static ssize_t (*orig)(const char *,char *,size_t);
 if(!orig) orig=dlsym(RTLD_NEXT,"readlink");
 if(!strncmp(path,"/proc/",6)) {
  const char *p=path+6;
  while(isdigit((unsigned char)*p)) ++p;
  if(p!=path+6 && !strcmp(p,"/exe")) path="/proc/self/exe";
 }
 return orig(path,buf,bufsiz);
}
