import re
from gmpy2 import *
import os.path
from qiskit.qasm import pi
import ast

#Takes RZQ Gate in form rzq(num, den) and transforms into rz((num/den)*pi). Overwrites file input
def rzq_to_rz(fname_in):
    count =  0
    line1 = []
    p_rzq = re.compile("rzq\((.*),(.*)\) q\[([0-9]+)\];")
    with open(str(fname_in), 'r') as f:
        data = f.readlines()
        for line in data:
            m1 = p_rzq.match(line)
            if m1:
                line1.append(count)
            count = count+1
    for i in range(len(line1)):
        a = p_rzq.match(data[line1[i]])
        num1 = int(a.group(1))
        num2 = int(a.group(2))
        q = int(a.group(3))
        t= mpq(int(num1), int(num2))
        y = float(mpfr(t, 53))
        data[line1[i]] = "rz(%s*pi) q[%d];\n" % (y, q)
    with open(str(fname_in), 'w') as f:
        f.writelines(data)
            
#Format from gates that are not compatible in Qiskit+VOQC and creates new file
#Decomposes CCZ, CCX, RZQ, U1, U2, U3
def format_from_qasm(fname):
    inqasm = open(fname, "r")
    tmp = open("copy.qasm", "w") # hardcoded filename
    p_ccz = re.compile("ccz (.*), (.*), (.*);")
    p_ccx = re.compile("ccx (.*), (.*), (.*);")
    p_rzq = re.compile("rzq\((.*),(.*)\) q\[([0-9]+)\];")
    p_u1 = re.compile("u1\((.*)\) q\[([0-9]+)\]")
    p_u2 = re.compile("u2\((.*),(.*)\) q\[([0-9]+)\]")
    p_u3 = re.compile("u3\((.*),(.*),(.*)\) q\[([0-9]+)\]")
    for line in inqasm:
        m1 = p_ccx.match(line)
        m2 = p_ccz.match(line)
        m3 = p_rzq.match(line)
        m4 = p_u1.match(line)
        m5 = p_u2.match(line)
        m6 = p_u2.match(line)
        if m1:
            a = m1.group(1)
            b = m1.group(2)
            c = m1.group(3)
            tmp.write("h %s;\n" % (c))
            tmp.write("cx %s, %s;\n" % (b, c))
            tmp.write("tdg %s;\n" % (c))
            tmp.write("cx %s, %s;\n" % (a, c))
            tmp.write("t %s;\n" % (c))
            tmp.write("cx %s, %s;\n" % (b, c))
            tmp.write("tdg %s;\n" % (c))
            tmp.write("cx %s, %s;\n" % (a, c))
            tmp.write("cx %s, %s;\n" % (a, b))
            tmp.write("tdg %s;\n" % (b))
            tmp.write("cx %s, %s;\n" % (a, b))
            tmp.write("t %s;\n" % (a))
            tmp.write("t %s;\n" % (b))
            tmp.write("t %s;\n" % (c))
            tmp.write("h %s;\n" % (c))
        elif m2:
            a = m2.group(1)
            b = m2.group(2)
            c = m2.group(3)
            tmp.write("cx %s, %s;\n" % (b, c))
            tmp.write("tdg %s;\n" % (c))
            tmp.write("cx %s, %s;\n" % (a, c))
            tmp.write("t %s;\n" % (c))
            tmp.write("cx %s, %s;\n" % (b, c))
            tmp.write("tdg %s;\n" % (c))
            tmp.write("cx %s, %s;\n" % (a, c))
            tmp.write("cx %s, %s;\n" % (a, b))
            tmp.write("tdg %s;\n" % (b))
            tmp.write("cx %s, %s;\n" % (a, b))
            tmp.write("t %s;\n" % (a))
            tmp.write("t %s;\n" % (b))
            tmp.write("t %s;\n" % (c))
        elif m3:
            num1 = int(m3.group(1))
            num2 = int(m3.group(2))
            q = int(m3.group(3))
            t= mpq(int(num1), int(num2))
            y = float(mpfr(t, 53))
            tmp.write("rz(%s*pi) q[%d];\n" % (y, q))
        elif m4:
            num1 = float(eval(m4.group(1)))
            q = int(m4.group(2))
            lamda = num1 - (pi/2)
            theta = 0
            phi = pi/2
            tmp.write("rz(%s) q[%d];\n" % (lamda, q))
            tmp.write ("h q[%d];\n" % (q))
            tmp.write ("rz(%s) q[%d];\n" % (theta, q))
            tmp.write ("h q[%d];\n" % (q))
            tmp.write ("rz(%s) q[%d];\n" % (phi, q))
        elif m5:
            num1 = m5.group(1)
            num1 = eval(num1)
            num2 = m5.group(2)
            num2 = eval(num2)
            d = int(m5.group(3))
            lamda = float(num2) - (pi/2)
            theta = pi/2
            phi = float(num1) + (pi/2)
            tmp.write("rz(%s) q[%d];\n" % (lamda, d))
            tmp.write ("h q[%d];\n" % (d))
            tmp.write ("rz(%s) q[%d];\n" % (theta, d))
            tmp.write ("h q[%d];\n" % (d))
            tmp.write ("rz(%s) q[%d];\n" % (phi, d))
            #tmp.write("u3(pi/2,%s,%s) q[%d];\n" % (num1,num2,d))
        elif m6:
            a = m.group(1)
            b = m.group(2)
            c = m.group(3)
            a = eval(a)
            b = eval(b)
            c = eval(c)
            d = int(m.group(4))
            lamda = float(c) - (pi/2)
            theta = float(a)
            phi = float(b) + (pi/2)
            tmp.write("rz(%s) q[%d];\n" % (lamda, d))
            tmp.write ("h q[%d];\n" % (d))
            tmp.write ("rz(%s) q[%d];\n" % (theta, d))
            tmp.write ("h q[%d];\n" % (d))
            tmp.write ("rz(%s) q[%d];\n" % (phi, d))  
        else:
            tmp.write(line)
    tmp.close()
    
#Undo multiplication of pi by Qiskit, and re-format for VOQC pass
def div_pi(fname):
    count = 0
    rz = []
    p_rz = re.compile("rz\(([-+]?(\d+(\.\d*)?|\.\d+)([eE][-+]?\d+)?)\) q\[([0-9]+)\];")
    with open(str(fname), 'r') as f:
        data = f.readlines()
        for line in data:
            m1 = p_rz.match(line)
            if m1:
                rz.append(count)
            count = count+1
    for i in range(len(rz)):
        a = p_rz.match(data[rz[i]])
        num1 = (float(a.group(1))/pi)
        q = int(a.group(5))
        data[rz[i]] = "rz(%s*pi) q[%d];\n" % (num1, q)

    with open(str(fname), 'w') as f:
        f.writelines(data)
