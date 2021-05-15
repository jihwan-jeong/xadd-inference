package util;

public class IntQuintuple {
    public int _i1;
    public int _i2;
    public int _i3;
    public int _i4;
    public int _i5;

    public IntQuintuple(int i1, int i2, int i3, int i4, int i5) {
        _i1 = i1;
        _i2 = i2;
        _i3 = i3;
        _i4 = i4;
        _i5 = i5;
    }

    public void set(int i1, int i2, int i3, int i4, int i5) {
        _i1 = i1;
        _i2 = i2;
        _i3 = i3;
        _i4 = i4;
        _i5 = i5;
    }

    // public int hashCode() {
    //     return (_i1) + (_i2 << 10) - (_i2 >>> 10) - (_i3 << 20) + (_i3 >>> 20) + (_i4) + (_i5);
    // }

    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + _i1;
        result = prime * result + _i2;
        result = prime * result + _i3;
        result = prime * result + _i4;
        result = prime * result + _i5;
        return result;
    }

    public boolean equals(Object o) {
        if (o instanceof IntQuintuple) {
            IntQuintuple t = (IntQuintuple) o;
            return this._i1 == t._i1
                    && this._i2 == t._i2
                    && this._i3 == t._i3
                    && this._i4 == t._i4
                    && this._i5 == t._i5;
        } else
            return false;
    }
}

