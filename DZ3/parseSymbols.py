# -*- coding: utf-8 -*-
def _parse_symbols(self):
    self._iter_lines(self._parse_macro)

    self._init_labels()
    self._iter_lines(self._parse_symbol)

    self._counter = 16

    self._iter_lines(self._parse_variable)


def _parse_symbol(self, line, p, o):

    if line[0] != "(" :
        return line


    else:
        # (@loop_start) spremiti da oznacava liniju 2

        label = line[1:].split(")")[0] # dohvati ime oznake
        label2 = line[1:].split(")")[1] # (neka_oznaka) A + B + C + D

        if len(label) == 0 :
            self._flag = False
            self._line = o
            self._errm = "Invalid label"

        elif label2 != "":
            self._flag = False
            self._line = o
            self._errm = "Invalid label"

        else:
            self._labels[label] = str(p)

    return ""


def _parse_macro(self, line, p, o):

    if line[0] != "$": #nije macro naredba
        return line

    #MV(A,B)
    #Sprema sadrzaj A u B

    naredba = line[1:].split("(")
    if naredba[0] == "MV":

        x =line[5:].split(")")[0]
        y= x.split(",") #splitati naredbu po zarezu da dobijemo A i B

        A = y[0]
        B = y[1]

        #@A
        #D = M
        #@B
        #M = D

        return ["@" + A,"D=M", "@" + B, "M=D"]

    elif naredba[0] == "SWP":
        #zamjenimo sadrzaje A i B registra -> SWP(A,B)

        x =line[5:].split(")")[0]
        y= x.split(",")

        A = y[0]
        B = y[1]

        #@A
        #D = M
        #@temp
        # M = D
        # @B
        # D = M
        # @A
        # M = D
        # @temp
        # D = M
        # @B
        # M = D

        return ["@" + A,"D=M", "@" + "temp","M=D","@"+B,"D=M","@"+A,"M=D","@"+"temp","D=M","@" + B,"M=D"]

    elif naredba[0] == "SUM":

         x = line[5:].split(")")[0]

         y = x.split(",")

         A = y[0]
         B = y[1]
         d = y[2]

         #zbrajam A i B i spremam ih u D

         # @A
         # D = M
         # @D
         # M = D
         # @B
         # D = M
         # @D
         # M = M + D

         return ["@" + A,"D=M","@" + d ,"M=D","@" + B, "D=M" ,"@" + d, "M=M+D"]

    elif naredba[0] == "WHILE":

        x = line[7:].split(")")[0]

        # (WHILE_START)
        # @x
        # D = M
        # (WHILE_END)
        # D; JEQ

        # Ideja je razlikovati svaki loop po i-u

        self._z.append(self._i)
        y = ["(WHILE_START" + str(self._i) + ")","@"+ x ,"D=M","@"+"WHILE_END"+str(self._i),"D;JEQ"]
        self._i += 1

        return y

    elif naredba[0] == "END":

        if len(self._z) != 0:

            r=self._z.pop()

            return ["@WHILE_START" + str(r), "0;JMP", "(WHILE_END" +  str(r) + ")"]

        else:
             self._flag = False
             self._line = o
             self._errm = "Error"


    else:
         self._flag = False
         self._line = o
         self._errm = "Invalid macro operation"


def _parse_variable(self, line, p, o):

    if line[0] != "@" :
        return line

    else:
        #@brojac
        var = line[1:] #odbacujemo @

        #@123
        if var.isdigit() == True:
            return line

        if var in self._labels.keys():
            return "@" + self._labels[var]

        elif var in self._variables.keys():
            return "@" + self._variables[var]

        else:
            self._variables[var] = str(self._counter)
            self._counter += 1
            return "@" + str(self._counter -1)



def _init_labels(self):
    self._labels = {
            "SCREEN" : "16384",
            "KBD" : "24576",
            "SP" : "0",
            "LCL" : "1",
            "ARG" : "2",
            "THIS" : "3",
            "THAT" : "4"}

    for i in range (0,16):
        self._labels["R" + str(i)] = str(i)

