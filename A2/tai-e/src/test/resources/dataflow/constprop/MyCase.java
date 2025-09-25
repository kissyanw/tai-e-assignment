class MyCase {

    private int m;

    void WithParameter(int x) {
        int a = x;
        if (a < 0) {
            a = 0;
        }
    }

    void CantHoldInt() {
        double a = 3.14;
        a += 1;
    }

    void LvalNonVar() {
        int a = 3;
        this.m = a;
    }

    void OtherExpression() {
        int a = 3;
        int b = -a;
    }

    void DivisionByZero(int nac) {
        int a = nac / 0;
        int b = a % 0;
        int c = 3 / 0;
    }
}
