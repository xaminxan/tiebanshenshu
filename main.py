import os
import sys
import csv
import datetime
import traceback
import pandas as pd

# 尝试导入 cnlunar
try:
    import cnlunar
except ImportError:
    print("【严重错误】: 未找到 'cnlunar' 模块，请运行: pip install cnlunar")
    sys.exit(1)

# ==============================================================================
# 0. 全局工具函数
# ==============================================================================
def input_datetime(desc_str):
    """处理用户输入的日期时间"""
    while True:
        try:
            dt_str = input(f"请输入{desc_str} (格式 YYYY-MM-DD HH:MM): ").strip()
            parts = dt_str.split()
            if len(parts) != 2:
                print("格式错误，日期和时间之间请用空格隔开。")
                continue
            date_str, time_str = parts
            year, month, day = map(int, date_str.split('-'))
            hour, minute = map(int, time_str.split(':'))
            if hour >= 23:
                print(f"  [提示] {hour}:{minute} 为晚子时，系统已自动按次日早子时排盘。")
                dt = datetime.datetime(year, month, day) + datetime.timedelta(days=1)
                return datetime.datetime(dt.year, dt.month, dt.day, 0, minute)
            return datetime.datetime(year, month, day, hour, minute)
        except ValueError:
            print("输入无效，请重新输入 (示例: 1951-10-14 18:00)")

def convert_to_bazi_info(dt_obj):
    """将公历转为八字信息"""
    try:
        a = cnlunar.Lunar(dt_obj, godType='8char')
        try: lm, ld = int(a.lunarMonth), int(a.lunarDay)
        except: lm, ld = 1, 1 
        return {
            "lunar_month": lm, "lunar_day": ld, "is_leap": "闰" in a.lunarMonthCn,
            "bazi": {"year": a.year8Char, "month": a.month8Char, "day": a.day8Char, "time": a.twohour8Char},
            "date_str": dt_obj.strftime("%Y-%m-%d %H:%M"),
            "lunar_str": f"{a.lunarYearCn}年 {a.lunarMonthCn}{a.lunarDayCn}"
        }
    except Exception as e:
        print(f"八字转换失败: {e}")
        return None

# ==============================================================================
# 1. 静态算法常量
# ==============================================================================
NAYIN_WUXING = {
    "甲子": "金", "乙丑": "金", "丙寅": "火", "丁卯": "火", "戊辰": "木", "己巳": "木",
    "庚午": "土", "辛未": "土", "壬申": "金", "癸酉": "金", "甲戌": "火", "乙亥": "火",
    "丙子": "水", "丁丑": "水", "戊寅": "土", "己卯": "土", "庚辰": "金", "辛巳": "金",
    "壬午": "木", "癸未": "木", "甲申": "水", "乙酉": "水", "丙戌": "土", "丁亥": "土",
    "戊子": "火", "己丑": "火", "庚寅": "木", "辛卯": "木", "壬辰": "水", "癸巳": "水",
    "甲午": "金", "乙未": "金", "丙申": "火", "丁酉": "火", "戊戌": "木", "己亥": "木",
    "庚子": "土", "辛丑": "土", "壬寅": "金", "癸卯": "金", "甲辰": "火", "乙巳": "火",
    "丙午": "水", "丁未": "水", "戊申": "土", "己酉": "土", "庚戌": "金", "辛亥": "金",
    "壬子": "木", "癸丑": "木", "甲寅": "水", "乙卯": "水", "丙辰": "土", "丁巳": "土",
    "戊午": "火", "己未": "火", "庚申": "木", "辛酉": "木", "壬戌": "水", "癸亥": "水"
}

LETTER_CORRECTION_MAP = {}
def build_correction_map():
    for c in "福分粉方务勿娼问": LETTER_CORRECTION_MAP[c] = 1
    for c in "器坷玄和": LETTER_CORRECTION_MAP[c] = 2
    for c in "忆召滞桃舌离誓绍": LETTER_CORRECTION_MAP[c] = 3
    for c in "龙吏鲁禄动弟社屯": LETTER_CORRECTION_MAP[c] = 4
    for c in "神肾物尾": LETTER_CORRECTION_MAP[c] = 5
    for c in "等亶旦刀西萨訾省": LETTER_CORRECTION_MAP[c] = 6
build_correction_map()

# ==============================================================================
# 2. 数据加载器
# ==============================================================================
class TieBanDataLoader:
    def __init__(self, db_folder="./数据库"):
        self.db_folder = db_folder
        self.tables = {} 
        self.rule_tables = []
        
        # 卦象映射表 - 支持按 (刻别, 本命数) 查找卦名
        self.HEXAGRAM_MAP = {}          # 兼容原有逻辑：仅按本命数查找（取优先匹配）
        self.HEXAGRAM_DETAIL_MAP = {}   # 完整映射：(刻别, 本命数) -> 卦名
        
        self.DESTINY_DATA = {}
        self.LIUNIAN_START = {}
        self.LIUNIAN_SEQ = {}
        self.MARKER_TABLE = {}
        self.LETTER_TABLE = {}
        self.SECRET_NUM_TABLE = {}
        
        # 14-14相关映射表
        self.DATA_BY_LETTER = {}        # (字母, 岁数) -> (基数, 加数, 条文校正数)
        self.DATA_BY_CORRECTION = {}    # (条文校正数, 岁数) -> (基数, 加数) 用于校正后查找
        self.CORRECTION_TO_LETTER = {}  # (条文校正数, 岁数) -> 字母 反向映射
        
        # 新增：条文断词映射表
        self.FORTUNE_DUANYU_MAP = {}    # 条文数字 -> (断语, 对应年龄)
        self.FORTUNE_DUANYU_RAW = []    # 原始断词数据
        
        print(f">>> 正在加载数据库 ({os.path.abspath(db_folder)})...")
        if os.path.exists(db_folder):
            self._load_all()
        else:
            print("【错误】数据库文件夹不存在！")

    def _read_csv_robust(self, filename, header_option=0):
        """健壮的读取函数，自动尝试多种编码"""
        path = os.path.join(self.db_folder, filename)
        if not os.path.exists(path): return None
        
        encodings = ['utf-8-sig', 'gbk', 'gb18030', 'utf-16']
        for enc in encodings:
            try:
                return pd.read_csv(path, header=header_option, encoding=enc)
            except Exception as e:
                continue
        return None

    def _read_csv_as_dicts(self, filename):
        """读取为字典列表 (带表头)"""
        df = self._read_csv_robust(filename, header_option=0)
        if df is not None:
            return df.to_dict('records')
        return []

    def _clean_key(self, val):
        if pd.isna(val) or val is None: return ""
        return str(val).strip().replace('\ufeff', '')
    
    def _is_numeric(self, value):
        """判断值是否可以转换为数字"""
        if pd.isna(value):
            return False
        try:
            float(value)
            return True
        except (ValueError, TypeError):
            return False

    def _load_all(self):
        # 1. 基础表 (14-1 ~ 14-6)
        self.tables['14-1'] = {self._clean_key(r.get('农历月份')): int(r.get('数值', 0)) for r in self._read_csv_as_dicts("14-1.csv")}
        self.tables['14-2'] = {self._clean_key(r.get('时支')): int(r.get('数值', 0)) for r in self._read_csv_as_dicts("14-2.csv")}
        for r in self._read_csv_as_dicts("14-3.csv"):
            if r.get('先天命数'):
                for n in r['先天命数'].split('|'): self.tables.setdefault('14-3', {})[int(n)] = {self._clean_key(k): v for k, v in r.items()}
        self.tables['14-4'] = {self._clean_key(r.get('五音')): int(r.get('数值', 0)) for r in self._read_csv_as_dicts("14-4.csv")}
        for r in self._read_csv_as_dicts("14-5.csv"):
            nayin = self._clean_key(r.get('日柱纳音'))
            self.tables.setdefault('14-5', {})[nayin] = {self._clean_key(k): int(v) for k, v in r.items() if k.strip() != '日柱纳音'}
        self.tables['14-6'] = {self._clean_key(r.get('时柱纳音')): int(r.get('数值', 0)) for r in self._read_csv_as_dicts("14-6.csv")}
        
        # 14-7 规则表
        self.rule_tables = self._read_csv_as_dicts("14-7.csv")
        
        # 2. 卦象表加载 (14-9.csv)
        df_14_9 = self._read_csv_robust("14-9.csv", header_option=None)
        if df_14_9 is not None and not df_14_9.empty:
            col_count = len(df_14_9.columns)
            print(f"  > 加载 14-9.csv 成功，共 {len(df_14_9)} 条数据，列数：{col_count}")
            
            if col_count >= 3:
                invalid_rows = 0
                valid_rows = 0
                
                for idx, row in df_14_9.iterrows():
                    try:
                        # 第一列：刻别（初刻/正刻）
                        kebie = self._clean_key(row[0])
                        if kebie not in ["初刻", "正刻"]:
                            invalid_rows += 1
                            if invalid_rows <= 3:
                                print(f"    提示: 第 {idx+1} 行刻别无效 ({kebie})，已跳过")
                            continue
                        
                        # 第二列：本命数
                        benming_num = row[1]
                        if not self._is_numeric(benming_num):
                            invalid_rows += 1
                            if invalid_rows <= 3:
                                print(f"    提示: 第 {idx+1} 行本命数非数值 ({benming_num})，已跳过")
                            continue
                        num = int(float(benming_num))
                        
                        # 第三列：卦名
                        hex_name = self._clean_key(row[2])
                        if not hex_name or hex_name == 'nan':
                            invalid_rows += 1
                            if invalid_rows <= 3:
                                print(f"    提示: 第 {idx+1} 行卦名为空，已跳过")
                            continue
                        
                        # 构建映射
                        self.HEXAGRAM_DETAIL_MAP[(kebie, num)] = hex_name
                        if num not in self.HEXAGRAM_MAP:
                            self.HEXAGRAM_MAP[num] = hex_name
                        
                        valid_rows += 1
                        if valid_rows <= 10:
                            print(f"    调试: {kebie} {num} -> {hex_name}")
                            
                    except Exception as e:
                        invalid_rows += 1
                        continue
                
                print(f"  > 14-9.csv 解析完成：有效行数 {valid_rows}，无效行数 {invalid_rows}")
                print(f"  > 成功解析 {len(self.HEXAGRAM_DETAIL_MAP)} 条详细卦象数据")
                if len(self.HEXAGRAM_DETAIL_MAP) == 0:
                    print("  [警告] 14-9.csv 中未找到有效卦象数据！")
        else:
            print("  [警告] 无法读取 14-9.csv，请检查文件是否存在！")

        # 14-10: 卦象详情
        for r in self._read_csv_as_dicts("14-10.csv"):
            try:
                gua = r['卦名']
                base = int(r['基数'])
                seq = int(r['序数'])
                def parse_offsets(s): 
                    return [int(x) for x in str(s).replace('，','|').split('|') if x.strip().isdigit()]
                offsets = {
                    "性格": parse_offsets(r['性格']),
                    "才能前程": parse_offsets(r['才能前程']),
                    "财运": parse_offsets(r['财运']),
                    "兄弟个数": parse_offsets(r['兄弟个数'])
                }
                data_pack = {"base": base, "seq": seq, "offsets": offsets}
                
                # 初刻
                if r.get('初刻先天'):
                    for n in str(r['初刻先天']).split('|'):
                        if n.strip().isdigit():
                            self.DESTINY_DATA[(gua, "Initial", int(n))] = data_pack
                # 正刻
                key_main = '正刻先天' if '正刻先天' in r else '正刻'
                if r.get(key_main):
                    for n in str(r[key_main]).split('|'):
                        if n.strip().isdigit():
                            self.DESTINY_DATA[(gua, "Main", int(n))] = data_pack
            except Exception: pass
            
        # 3. 流年相关 (14-11 ~ 14-14)
        for r in self._read_csv_as_dicts("14-11-1.csv"):
            try:
                num = int(r['先天命数']) if '先天命数' in r else 'generic'
                if r.get('年支组') and r.get('性别'):
                    self.LIUNIAN_START[(num, self._clean_key(r['年支组']), self._clean_key(r['性别']))] = int(r.get('起始数', 0))
            except: pass
            
        for r in self._read_csv_as_dicts("14-11-2.csv"):
            try:
                num = int(r.get('先天命数', 0))
                gan = self._clean_key(r.get('天干') or r.get('年干组'))
                seq = []
                if '1' in r and '12' in r:
                    seq = [self._clean_key(r.get(str(i))) for i in range(1, 13)]
                elif '原始序列' in r:
                    seq = [x.strip() for x in r['原始序列'].replace(',', '|').replace(' ', '|').split('|') if x.strip()]
                if num and gan and seq: self.LIUNIAN_SEQ[(num, gan)] = seq
            except: pass
            
        for r in self._read_csv_as_dicts("14-12.csv"):
            try:
                zhi = self._clean_key(r.get('流年地支'))
                num = int(r.get('后天命数', 0))
                marker = self._clean_key(r.get('流年标记'))
                if zhi and num and marker: self.MARKER_TABLE.setdefault(zhi, {})[num] = marker
            except: pass
            
        for r in self._read_csv_as_dicts("14-13.csv"):
            try:
                moment = self._clean_key(r.get('考刻'))
                parity = self._clean_key(r.get('日命数加时运数的奇偶性'))
                tone_val = self._clean_key(r.get('流年天四声'))
                marker = self._clean_key(r.get('流年标记'))
                letter = self._clean_key(r.get('流年字母'))
                if moment and parity and tone_val and marker and letter:
                     self.LETTER_TABLE[(moment, parity, tone_val, marker)] = letter
            except: pass
        
        # 14-14 流年条文表
        df_14_14 = self._read_csv_robust("14-14.csv", header_option=0)
        if df_14_14 is not None and not df_14_14.empty:
            print(f"  > 加载 14-14.csv 成功，共 {len(df_14_14)} 条数据")
            
            # 获取列名并清洗
            columns = [self._clean_key(col) for col in df_14_14.columns]
            print(f"    14-14.csv 列名: {columns}")
            
            # 查找关键列的索引
            col_mapping = {}
            for idx, col in enumerate(columns):
                if '流年字母' in col:
                    col_mapping['letter'] = idx
                elif '流年岁数' in col:
                    col_mapping['age'] = idx
                elif '基数' in col:
                    col_mapping['base'] = idx
                elif '加数' in col:
                    col_mapping['add'] = idx
                elif '条文校正数' in col or '流年叫正文' in col:
                    col_mapping['correction'] = idx
            
            # 验证必要列是否存在
            required_cols = ['letter', 'age', 'base', 'add', 'correction']
            missing_cols = [col for col in required_cols if col not in col_mapping]
            if missing_cols:
                print(f"    [警告] 14-14.csv 缺少必要列: {missing_cols}")
            else:
                # 读取数据
                for idx, row in df_14_14.iterrows():
                    try:
                        letter = self._clean_key(row[col_mapping['letter']])
                        age = int(float(row[col_mapping['age']]))
                        base = int(float(row[col_mapping['base']]))
                        add = int(float(row[col_mapping['add']]))
                        correction = int(float(row[col_mapping['correction']]))
                        
                        if letter and age > 0:
                            # 主映射：(字母, 岁数) -> (基数, 加数, 条文校正数)
                            self.DATA_BY_LETTER[(letter, age)] = (base, add, correction)
                            # 校正映射：(条文校正数, 岁数) -> (基数, 加数)
                            self.DATA_BY_CORRECTION[(correction, age)] = (base, add)
                            # 反向映射：(条文校正数, 岁数) -> 字母
                            self.CORRECTION_TO_LETTER[(correction, age)] = letter
                            
                    except Exception as e:
                        continue
                
                print(f"    成功加载 {len(self.DATA_BY_LETTER)} 条流年条文数据")
        else:
            print("  [警告] 无法读取 14-14.csv，请检查文件是否存在！")
        
        # 新增：加载铁板神数-条文断词.csv
        duanyu_file = "铁板神数-条文断词.csv"
        df_duanyu = self._read_csv_robust(duanyu_file, header_option=0)
        if df_duanyu is not None and not df_duanyu.empty:
            print(f"  > 加载 {duanyu_file} 成功，共 {len(df_duanyu)} 条数据")
            
            # 获取列名并清洗
            columns = [self._clean_key(col) for col in df_duanyu.columns]
            print(f"    {duanyu_file} 列名: {columns}")
            
            # 查找关键列的索引
            col_mapping = {}
            for idx, col in enumerate(columns):
                if '条文数字' in col or '条文数' in col or '数字' in col:
                    col_mapping['num'] = idx
                elif '断语' in col or '断词' in col or '内容' in col:
                    col_mapping['duanyu'] = idx
                elif '年龄' in col or '对应年龄' in col or '岁数' in col:
                    col_mapping['age'] = idx
            
            # 读取数据
            valid_count = 0
            for idx, row in df_duanyu.iterrows():
                try:
                    # 获取条文数字
                    if 'num' in col_mapping:
                        fortune_num = row[col_mapping['num']]
                        if self._is_numeric(fortune_num):
                            fortune_num = int(float(fortune_num))
                        else:
                            continue
                    else:
                        continue
                    
                    # 获取断语
                    duanyu = ""
                    if 'duanyu' in col_mapping:
                        duanyu = self._clean_key(row[col_mapping['duanyu']])
                    
                    # 获取对应年龄
                    duanyu_age = ""
                    if 'age' in col_mapping:
                        duanyu_age = self._clean_key(row[col_mapping['age']])
                    
                    # 构建映射
                    if fortune_num > 0:
                        self.FORTUNE_DUANYU_MAP[fortune_num] = (duanyu, duanyu_age)
                        self.FORTUNE_DUANYU_RAW.append({
                            'num': fortune_num,
                            'duanyu': duanyu,
                            'age': duanyu_age
                        })
                        valid_count += 1
                        
                except Exception as e:
                    continue
            
            print(f"    成功加载 {valid_count} 条条文断语数据")
            if valid_count > 0:
                # 打印前5条作为示例
                print(f"    示例数据: {list(self.FORTUNE_DUANYU_MAP.items())[:5]}")
        else:
            print(f"  [警告] 无法读取 {duanyu_file}，断语功能将不可用！")

# ==============================================================================
# 3. Calculator
# ==============================================================================
class TieBanCalculator:
    def __init__(self):
        self.loader = TieBanDataLoader()
        self.db = self.loader
        self.tiangan = ["甲", "乙", "丙", "丁", "戊", "己", "庚", "辛", "壬", "癸"]
        self.dizhi = ["子", "丑", "寅", "卯", "辰", "巳", "午", "未", "申", "酉", "戌", "亥"]

    def get_gan_group(self, gan):
        if gan not in self.tiangan: return "甲己"
        return ["甲己", "乙庚", "丙辛", "丁壬", "戊癸"][self.tiangan.index(gan) % 5]

    def get_liunian_groups(self, year_gan, year_zhi):
        b_group = "未知"
        if year_zhi in "寅午戌": b_group = "寅午戌"
        elif year_zhi in "申子辰": b_group = "申子辰"
        elif year_zhi in "巳酉丑": b_group = "巳酉丑"
        elif year_zhi in "亥卯未": b_group = "亥卯未"
        s_group = "未知"
        if year_gan in "甲乙丙丁": s_group = "甲乙丙丁"
        elif year_gan in "戊己": s_group = "戊己"
        elif year_gan in "庚辛": s_group = "庚辛"
        elif year_gan in "壬癸": s_group = "壬癸"
        return b_group, s_group

    def is_yang_year(self, year_gan):
        return year_gan in ["甲", "丙", "戊", "庚", "壬"]
    
    def calculate_correction(self, original_correction, age):
        """
        根据年龄计算校正后的条文校正数
        规则：
        1. 1-10岁/81-108岁：校正数+2（>6则-6）
        2. 其他年龄：校正数+3（>20则-20）
        """
        if original_correction == 0:
            return 0
            
        # 情况一：1-10岁 或 81-108岁
        if (1 <= age <= 10) or (81 <= age <= 108):
            new_correction = original_correction + 2
            if new_correction > 6:
                new_correction -= 6
        # 情况二：其他年龄
        else:
            new_correction = original_correction + 3
            if new_correction > 20:
                new_correction -= 20
                
        return new_correction
    
    def get_fortune_duanyu(self, fortune_num):
        """
        根据条文数字获取对应的断语和年龄
        返回：(断语, 对应年龄)
        """
        if not fortune_num or fortune_num == "" or not self._is_numeric(fortune_num):
            return ("", "")
        
        try:
            num = int(float(fortune_num))
            return self.db.FORTUNE_DUANYU_MAP.get(num, ("未找到断语", "未知"))
        except:
            return ("", "")
    
    def _is_numeric(self, value):
        """判断值是否可以转换为数字"""
        if not value:
            return False
        try:
            float(value)
            return True
        except (ValueError, TypeError):
            return False

    def calculate(self, payload):
        birth, query, gender = payload['birth_info'], payload['query_info'], payload['gender']
        y_gan, y_zhi = birth['bazi']['year'][0], birth['bazi']['year'][1]
        t_zhi = birth['bazi']['time'][1]
        d_day, t_gan, t_time = birth['bazi']['day'], query['bazi']['time'][0], query['bazi']['time']
        
        details = {}
        details['header_info'] = f"性别:{gender}, 农历:{birth['lunar_str']}，闰月{'是' if birth['is_leap'] else '否'}，出生八字：{birth['bazi']['year']} {birth['bazi']['month']} {birth['bazi']['day']} {birth['bazi']['time']}\n求测日期：阳历：{query['date_str']}     八字：{query['bazi']['year']} {query['bazi']['month']} {query['bazi']['day']} {query['bazi']['time']}"

        # Step 1: 计算先天命数
        calc_month = str(m_idx := birth['lunar_month'] + (1 if birth['is_leap'] else 0))
        if int(m_idx) > 12: calc_month = "1"
        month_val = self.db.tables['14-1'].get(calc_month, int(calc_month))
        time_val = self.db.tables['14-2'].get(t_zhi, 0)
        cong_num = month_val + 3 - time_val
        if cong_num <= 0: cong_num += 12
        details['cong_calc'] = f"先天命数 = {cong_num}"
        details['cong_num'] = cong_num

        # Step 2: 计算五音命数
        gan_group = self.get_gan_group(y_gan)
        tone = self.db.tables.get('14-3', {}).get(cong_num, {}).get(gan_group, "宫")
        tone_num = self.db.tables['14-4'].get(tone, 5)
        details['tone_num'] = tone_num

        # Step 3: 计算日命数和时运数
        day_n = NAYIN_WUXING.get(d_day, "金")
        day_life = self.db.tables.get('14-5', {}).get(day_n, {}).get(t_gan, 0)
        time_n = NAYIN_WUXING.get(t_time, "金")
        time_luck = self.db.tables['14-6'].get(time_n, 0)
        details['day_life_calc'] = f"日命:{day_life}, 时运:{time_luck}"

        # Step 4: 确定刻别（初刻/正刻）
        sum_val = day_life + time_luck
        is_yang = self.is_yang_year(y_gan)
        grp = "阳男阴女" if (gender == "男" and is_yang) or (gender == "女" and not is_yang) else "阴男阳女"
        cond = ">6" if sum_val > 6 else "<=6"
        moment = "Main"
        for r in self.db.rule_tables:
            if r['组别'] == grp and r['和值条件'] == cond:
                moment = "Initial" if r['刻别'] == "初刻" else "Main"
                break
        moment_cn = "初刻" if moment == "Initial" else "正刻"
        details['moment_calc'] = f"考刻: {moment_cn} ({grp})"
        details['moment_cn'] = moment_cn

        # Step 5: 计算本命数
        base_val = tone_num * 5 + day_life + time_luck
        fact = (base_val - 1) if sum_val <= 6 else (base_val - 6)
        main_num = fact * 30 + birth['lunar_day']
        details['main_calc'] = f"本命数: {main_num}"
        details['main_num'] = main_num

        # Step 6: 查找卦名
        hex_name = self.db.HEXAGRAM_DETAIL_MAP.get((moment_cn, main_num), 
                                                  self.db.HEXAGRAM_MAP.get(main_num, 
                                                                          f"未知(刻别:{moment_cn},本命数:{main_num}未匹配)"))
        details['hex_name'] = hex_name
        
        # 查找详细数据
        tbl_data = self.db.DESTINY_DATA.get((hex_name, moment, cong_num))
        details['tbl_data'] = tbl_data

        # Step 7: 计算后天命数
        pn_sum = cong_num + main_num
        pn_num = pn_sum % 8
        if pn_num == 0: pn_num = 8
        details['pn_log'] = f"先天命数＋本命数＝{cong_num}＋{main_num}＝{pn_sum}÷8→余数＝{pn_num}"
        details['pn_num'] = pn_num

        # Step 8: 计算流年条文（核心修改）
        liunian = []
        try:
            bg, sg = self.get_liunian_groups(y_gan, y_zhi)
            start = 0
            for k in [(cong_num, bg, gender), ('generic', bg, gender)]:
                if k in self.db.LIUNIAN_START:
                    start = self.db.LIUNIAN_START[k]; break
            raw_seq = []
            final_seq = ["?"] * 12
            if start != 0:
                for k in [(cong_num, y_gan), (cong_num, sg)]:
                    if k in self.db.LIUNIAN_SEQ:
                        raw_seq = self.db.LIUNIAN_SEQ[k]; break
                if raw_seq and len(raw_seq) >= 12:
                    off = (13 - start) % 12
                    final_seq = [raw_seq[(i + off) % 12] for i in range(12)]

            tg_list = ["甲", "乙", "丙", "丁", "戊", "己", "庚", "辛", "壬", "癸"]
            dz_list = ["子", "丑", "寅", "卯", "辰", "巳", "午", "未", "申", "酉", "戌", "亥"]
            st_tg = tg_list.index(y_gan)
            st_dz = dz_list.index(y_zhi)
            
            # 生成1-108岁的流年数据（覆盖81-108岁的校正需求）
            for age in range(1, 109):
                cur_tg = tg_list[(st_tg + age - 1) % 10]
                cur_dz = dz_list[(st_dz + age - 1) % 12]
                sound = final_seq[(age - 1) % 12] if final_seq[0] != "?" else "?"
                marker = self.db.MARKER_TABLE.get(cur_dz, {}).get(pn_num, "?")
                
                age_parity = "奇数" if age % 2 != 0 else "偶数"
                letter = self.db.LETTER_TABLE.get((moment_cn, age_parity, sound, marker), "?")

                # 初始化变量
                base = 0
                add = 0
                original_correction = 0  # 原始条文校正数
                corrected_correction = 0  # 校正后的条文校正数
                original_fortune = ""     # 原始条文数
                corrected_fortune = ""    # 校正后的条文数
                formula = ""
                corrected_letter = ""     # 校正后的字母
                
                # 查找原始数据
                if letter != "?" and (letter, age) in self.db.DATA_BY_LETTER:
                    base, add, original_correction = self.db.DATA_BY_LETTER[(letter, age)]
                    formula = f"{base}+{add}"
                    original_fortune = str(base + add)
                    
                    # 计算校正后的条文校正数
                    corrected_correction = self.calculate_correction(original_correction, age)
                    
                    # 根据新的校正数查找校正后的条文
                    if corrected_correction > 0 and (corrected_correction, age) in self.db.DATA_BY_CORRECTION:
                        corr_base, corr_add = self.db.DATA_BY_CORRECTION[(corrected_correction, age)]
                        corrected_fortune = str(corr_base + corr_add)
                        # 查找校正后的字母（可选）
                        corrected_letter = self.db.CORRECTION_TO_LETTER.get((corrected_correction, age), "?")
                
                # ========== 新增：获取断语信息 ==========
                # 原始条文断语
                original_duanyu, original_duanyu_age = self.get_fortune_duanyu(original_fortune)
                # 校正后条文断语
                corrected_duanyu, corrected_duanyu_age = self.get_fortune_duanyu(corrected_fortune)
                
                # 构建流年数据
                liunian.append({
                    "age": age, 
                    "year": f"{cur_tg}{cur_dz}", 
                    "sound": sound,
                    "marker": marker, 
                    "letter": letter,
                    "corrected_letter": corrected_letter,
                    "original_correction": str(original_correction),
                    "corrected_correction": str(corrected_correction),
                    "formula": formula, 
                    "original_fortune": original_fortune,
                    "corrected_fortune": corrected_fortune,
                    # 新增断语字段
                    "original_duanyu": original_duanyu,          # 原始条文断语
                    "original_duanyu_age": original_duanyu_age,  # 原始条文对应年龄
                    "corrected_duanyu": corrected_duanyu,        # 校正后条文断语
                    "corrected_duanyu_age": corrected_duanyu_age # 校正后条文对应年龄
                })
        except Exception as e:
            print(f"计算流年数据时出错: {e}")
            traceback.print_exc()
            pass
            
        details['liunian'] = liunian
        return details

    def print_report(self, res):
        print("\n" + "="*220)
        print(res['header_info'])
        print("="*220 + "\n")
        
        print("【基础排盘信息】")
        print(f"{res['cong_calc']}")
        print(f"五音命数 = {res['tone_num']}")
        print(f"{res['day_life_calc']}")
        print(f"{res['moment_calc']}")
        print(f"{res['main_calc']}")
        print(f"十二辟卦: {res['hex_name']}")
        
        print("\n【本命条文】")
        if res['tbl_data']:
            tbl = res['tbl_data']
            base, seq, offsets = tbl['base'], tbl['seq'], tbl['offsets']
            print(f"十二辟卦 —— {res['hex_name']}  +{base}")
            print(f"{res['moment_cn']}生人  先天命数 {res['cong_num']}")
            print("-" * 60)
            print(f"{'序数':<6}{'性格':<10}{'才能前程':<10}{'财运':<10}{'兄弟个数':<10}")
            s_char = ",".join(map(str, offsets['性格']))
            s_car = ",".join(map(str, offsets['才能前程']))
            s_wea = ",".join(map(str, offsets['财运']))
            s_bro = ",".join(map(str, offsets['兄弟个数']))
            print(f"{seq:<6}{s_char:<10}{s_car:<10}{s_wea:<10}{s_bro:<10}")
            print("-" * 60)
            print("\n本命条文详细计算：")
            def print_calc(title, offset_list):
                for off in offset_list:
                    print(f"  {title}: {base} + {seq} + {off} = {base+seq+off}")
            print_calc("(1) 性格", offsets['性格'])
            print_calc("(2) 才能、前程", offsets['才能前程'])
            print_calc("(3) 财运", offsets['财运'])
            print_calc("(4) 兄弟个数", offsets['兄弟个数'])
        else:
            print(f"  [提示] 未在 14-10 表中找到匹配的条文数据 (卦名: {res['hex_name']}, 刻别: {res['moment_cn']}, 先天数: {res['cong_num']})")

        print("\n【流年条文 (1-100岁)】")
        print("=" * 220)
        # 打印表头（包含断语列）
        header_parts = [
            f"{'岁数':<6}", f"{'干支':<6}", f"{'四声':<6}", f"{'标记':<6}", f"{'字母':<6}",
            f"{'校正数':<8}", f"{'校正后校正数':<12}", f"{'计算公式':<10}",
            f"{'原条文':<8}", f"{'原断语':<30}", f"{'原断语年龄':<10}",
            f"{'校正后条文':<10}", f"{'校正后断语':<30}", f"{'校正后断语年龄':<10}"
        ]
        print("".join(header_parts))
        print("=" * 220)
        
        # 打印1-100岁的流年数据
        for i in [item for item in res['liunian'] if 1 <= item['age'] <= 100]:
            # 截断过长的断语，保持表格整洁
            original_duanyu = i['original_duanyu'][:28] + ".." if len(i['original_duanyu']) > 30 else i['original_duanyu']
            corrected_duanyu = i['corrected_duanyu'][:28] + ".." if len(i['corrected_duanyu']) > 30 else i['corrected_duanyu']
            
            row_parts = [
                f"{i['age']:<6}", f"{i['year']:<6}", f"{i['sound']:<6}", f"{i['marker']:<6}", f"{i['letter']:<6}",
                f"{i['original_correction']:<8}", f"{i['corrected_correction']:<12}", f"{i['formula']:<10}",
                f"{i['original_fortune']:<8}", f"{original_duanyu:<30}", f"{i['original_duanyu_age']:<10}",
                f"{i['corrected_fortune']:<10}", f"{corrected_duanyu:<30}", f"{i['corrected_duanyu_age']:<10}"
            ]
            print("".join(row_parts))
        print("=" * 220)

    def save_to_md(self, res, b_str, q_str):
        """保存排盘结果到Markdown文件"""
        if not os.path.exists("output"):
            os.makedirs("output")
        
        fname = f"output/铁板排盘_{b_str.split()[0]}_{q_str.split()[0]}.md"
        with open(fname, "w", encoding="utf-8") as f:
            # 写入基础信息
            f.write("# 铁板神数排盘结果\n\n")
            f.write(f"**排盘时间**: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
            f.write(f"## 基础信息\n")
            f.write(f"```\n{res['header_info']}\n```\n\n")
            
            # 写入基础排盘数据
            f.write("## 基础排盘\n")
            f.write(f"- 先天命数：{res['cong_calc']}\n")
            f.write(f"- 五音命数：{res['tone_num']}\n")
            f.write(f"- 日命数 & 时运数：{res['day_life_calc']}\n")
            f.write(f"- 考刻结果：{res['moment_calc']}\n")
            f.write(f"- 本命数：{res['main_calc']}\n")
            f.write(f"- 十二辟卦：{res['hex_name']}\n\n")
            
            # 写入本命条文
            f.write("## 本命条文\n")
            if res['tbl_data']:
                tbl = res['tbl_data']
                base, seq, offsets = tbl['base'], tbl['seq'], tbl['offsets']
                f.write(f"**{res['moment_cn']}生人 - 先天命数 {res['cong_num']} - {res['hex_name']}(+{base})**\n\n")
                f.write("| 项目 | 数值 | 计算公式 |\n")
                f.write("|------|------|----------|\n")
                f.write(f"| 序数 | {seq} | - |\n")
                for item, values in offsets.items():
                    for val in values:
                        total = base + seq + val
                        f.write(f"| {item} | {total} | {base} + {seq} + {val} = {total} |\n")
            else:
                f.write("未找到匹配的本命条文数据\n\n")
            
            # 写入流年条文表格（包含断语）
            f.write("## 流年条文 (1-100岁)\n")
            f.write("| 岁数 | 干支 | 四声 | 标记 | 字母 | 校正数 | 校正后校正数 | 计算公式 | 原条文 | 原断语 | 原断语年龄 | 校正后条文 | 校正后断语 | 校正后断语年龄 |\n")
            f.write("|------|------|------|------|------|--------|--------------|----------|--------|--------|------------|------------|------------|----------------|\n")
            
            for i in [item for item in res['liunian'] if 1 <= item['age'] <= 100]:
                # 处理Markdown中的特殊字符
                original_duanyu = i['original_duanyu'].replace('|', '｜').replace('\n', ' ')
                corrected_duanyu = i['corrected_duanyu'].replace('|', '｜').replace('\n', ' ')
                
                f.write(f"| {i['age']} | {i['year']} | {i['sound']} | {i['marker']} | {i['letter']} | "
                        f"{i['original_correction']} | {i['corrected_correction']} | {i['formula']} | "
                        f"{i['original_fortune']} | {original_duanyu} | {i['original_duanyu_age']} | "
                        f"{i['corrected_fortune']} | {corrected_duanyu} | {i['corrected_duanyu_age']} |\n")
        
        print(f"\n[完成] 排盘报告已保存至: {os.path.abspath(fname)}")

def main():
    print("="*60 + "\n  铁板神数排盘系统 (完整版)\n" + "="*60)
    try:
        # 获取性别
        while True:
            g = input("\n请输入性别 (1:男, 2:女): ").strip()
            if g in ['1', '男']:
                gender = "男"
                break
            elif g in ['2', '女']:
                gender = "女"
                break
            else:
                print("输入无效，请输入 1 或 2")
        
        # 获取时间
        print("\n【时间输入说明】格式为 YYYY-MM-DD HH:MM，例如：1990-01-01 12:00")
        dt_b = input_datetime("出生时间")
        dt_q = input_datetime("求测时间")
        
        # 转换为八字信息
        print("\n>>> 正在转换八字信息...")
        info_b = convert_to_bazi_info(dt_b)
        info_q = convert_to_bazi_info(dt_q)
        
        if not info_b:
            print("【错误】出生时间转换失败！")
            return
        if not info_q:
            print("【错误】求测时间转换失败！")
            return
        
        # 开始排盘
        print("\n>>> 正在进行铁板神数排盘...")
        calculator = TieBanCalculator()
        result = calculator.calculate({
            "birth_info": info_b, 
            "query_info": info_q, 
            "gender": gender
        })
        
        # 打印报告
        calculator.print_report(result)
        
        # 保存文件
        calculator.save_to_md(result, info_b['date_str'], info_q['date_str'])
        
    except KeyboardInterrupt:
        print("\n\n程序已被用户中断")
    except Exception as e:
        print(f"\n\n程序运行出错: {e}")
        traceback.print_exc()

if __name__ == "__main__":
    main()