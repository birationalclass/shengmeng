package main
import("net/http/httptest";"os";"path/filepath";"testing";"strings")
func TestOfflineFilesAndAudioRange(t *testing.T){
 root:=t.TempDir();os.MkdirAll(filepath.Join(root,"visuals","math-refuge"),0755)
 os.WriteFile(filepath.Join(root,"visuals","math-refuge","index.html"),[]byte("offline-ready"),0644)
 os.WriteFile(filepath.Join(root,"sample.mp3"),[]byte("0123456789"),0644)
 h:=handler(root)
 for _,x:=range []struct{path string;status int;want string}{{"/visuals/math-refuge/",200,"offline-ready"},{"/__refuge_health",200,"native runtime"},{"/missing",404,"404"},{"/",404,"404"}}{
  w:=httptest.NewRecorder();h.ServeHTTP(w,httptest.NewRequest("GET",x.path,nil));if w.Code!=x.status||!strings.Contains(w.Body.String(),x.want){t.Fatalf("%s: %d %s",x.path,w.Code,w.Body.String())}
 }
 w:=httptest.NewRecorder();r:=httptest.NewRequest("GET","/sample.mp3",nil);r.Header.Set("Range","bytes=2-5");h.ServeHTTP(w,r)
 if w.Code!=206||w.Body.String()!="2345"{t.Fatalf("audio range: %d %s",w.Code,w.Body.String())}
}
