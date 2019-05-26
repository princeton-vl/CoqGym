#include <caml/mlvalues.h>

extern int cplus(int, int);

CAMLprim value
camlplus(value vx, value vy)
{
    int x = Int_val(vx);
    int y = Int_val(vy);
    return Val_int(cplus(x, y));
}
