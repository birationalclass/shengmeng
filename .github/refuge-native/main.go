// Math Refuge offline launcher. Standard library only, no installation or runtime required.
package main

import (
 "context"
 "flag"
 "fmt"
 "log"
 "net"
 "net/http"
 "os"
 "os/exec"
 "os/signal"
 "path/filepath"
 "runtime"
 "strings"
 "time"
)

func handler(root string) http.Handler {
 files := http.FileServer(http.Dir(root))
 return http.HandlerFunc(func(w http.ResponseWriter,r *http.Request){
  if r.URL.Path=="/__refuge_health" {w.Header().Set("Content-Type","text/plain; charset=utf-8");fmt.Fprint(w,"Math Refuge local / native runtime\n");return}
  clean:=filepath.Clean(filepath.FromSlash(r.URL.Path))
  for _,part:=range strings.Split(filepath.ToSlash(clean),"/"){if strings.HasPrefix(part,".") && part!="." {http.NotFound(w,r);return}}
  p:=filepath.Join(root,clean)
  st,err:=os.Stat(p)
  if err!=nil {http.NotFound(w,r);return}
  if st.IsDir(){if _,err=os.Stat(filepath.Join(p,"index.html"));err!=nil{http.NotFound(w,r);return}}
  w.Header().Set("X-Content-Type-Options","nosniff")
  if strings.HasSuffix(r.URL.Path,".mjs")||strings.HasSuffix(r.URL.Path,".js"){w.Header().Set("Content-Type","text/javascript; charset=utf-8")}
  files.ServeHTTP(w,r)
 })
}
func findRoot() string {
 exe,err:=os.Executable();if err!=nil{return "."}
 p:=filepath.Dir(exe)
 for i:=0;i<4;i++ {if _,err:=os.Stat(filepath.Join(p,"visuals","math-refuge","index.html"));err==nil{return p};p=filepath.Dir(p)}
 return filepath.Dir(exe)
}
func openBrowser(url string) error {
 var cmd *exec.Cmd
 switch runtime.GOOS {case "darwin":cmd=exec.Command("/usr/bin/open",url);case "windows":cmd=exec.Command("rundll32.exe","url.dll,FileProtocolHandler",url);default:cmd=exec.Command("xdg-open",url)}
 return cmd.Run()
}
func main(){
 root:=flag.String("root",findRoot(),"package folder")
 noBrowser:=flag.Bool("no-browser",false,"do not open browser")
 urlFile:=flag.String("url-file","","write local URL for validation")
 flag.Parse()
 abs,err:=filepath.Abs(*root);if err!=nil{log.Fatal(err)}
 if _,err=os.Stat(filepath.Join(abs,"visuals","math-refuge","index.html"));err!=nil{log.Fatal("Please extract the complete package first / 请先完整解压离线包")}
 ln,err:=net.Listen("tcp4","127.0.0.1:0");if err!=nil{log.Fatal(err)}
 url:="http://"+ln.Addr().String()+"/visuals/math-refuge/"
 fmt.Println("数学难民营 · 免安装本地版 / Math Refuge Local")
 fmt.Println(url)
 fmt.Println("保留此窗口；关闭窗口或按 Ctrl+C 停止。无需 Python / Node / 联网。")
 if *urlFile!="" {if err=os.WriteFile(*urlFile,[]byte(url),0600);err!=nil{log.Fatal(err)}}
 srv:=&http.Server{Handler:handler(abs),ReadHeaderTimeout:10*time.Second}
 signals:=make(chan os.Signal,1);signal.Notify(signals,os.Interrupt)
 go func(){<-signals;ctx,cancel:=context.WithTimeout(context.Background(),3*time.Second);defer cancel();srv.Shutdown(ctx)}()
 if !*noBrowser {go func(){time.Sleep(250*time.Millisecond);if err:=openBrowser(url);err!=nil{fmt.Println("请手动打开上方本机地址 / Open the address above in your browser")}}()}
 if err=srv.Serve(ln);err!=nil&&err!=http.ErrServerClosed{log.Fatal(err)}
}
