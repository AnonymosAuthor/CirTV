
class SymDataDic:
    def __init__(self, sym_path, all_signals, one):
        self.__s_dic = dict()
        self.__w_dic_r = dict()
        self.__w_dic = dict()
        self.__c_dic = dict()
        self.__signal_dic = dict()
        file = open(sym_path, 'r')
        content = file.readlines()
        file.close()

        self.__w_dic_r['0'] = one

        for line in content:
            data = line.replace('\n', '').split(',')
            sym_name = data[3]
            self.__s_dic[sym_name] = data[0]
            self.__w_dic[sym_name] = data[1]
            self.__w_dic_r[data[1]] = sym_name
            self.__c_dic[sym_name] = data[2]

        for signal in all_signals:
            self.__signal_dic[signal.sym_name] = signal

    def get_s(self, sym_name):
        return self.__s_dic[sym_name]

    def get_w(self, sym_name):
        return self.__w_dic[sym_name]

    def get_c(self, sym_name):
        return self.__c_dic[sym_name]

    # 依照下标进行获取对应signal表达式
    def get_w_item(self, w_add):
        if w_add == '0':
            return self.__w_dic_r[w_add]
        else:
            sym_name = self.__w_dic_r[w_add]
            signal = self.__signal_dic[sym_name]
            return signal.toSmt()
