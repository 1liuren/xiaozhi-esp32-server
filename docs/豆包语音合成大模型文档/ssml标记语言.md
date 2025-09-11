SSML标记语言
最近更新时间：2025.03.14 14:49:28
首次发布时间：2024.08.09 17:58:04
我的收藏
有用
无用
说明

Universal SSML是Flute统一TTS前端（Universal FrontEnd，简称UFE）采用的与具体语种解耦的SSML框架，能够方便地为不同语种提供SSML能力。

注：双向流式API目前不支持SSML

关于SSML
SSML是语音合成标记语言（Speech Synthesis Markup Language）的缩写。它是W3C的语音接口框架的一部分，通过SSML，可以对语音合成的效果进行定制化。

关于Universal SSML
Universal SSML是Flute统一TTS前端（Universal FrontEnd，简称UFE）采用的与具体语种解耦的SSML框架，能够方便地为不同语种提供SSML能力。

说明

如果使用中英混音色，需要注意比较短的英文句子可能被语种识别为中文，部分标签在中文和英文场景下表现不同。例如在中文场景下，如果Verbatim内的文本是有效单词则不会按字母读。


必读
注意

接口传参时，请选择 text_type=ssml
所有文本 需放在 <speak></speak>标签之内
不同语种模型可使用的标签不同，请严格按照下表进行请求，否则会系统报错
当前仅支持中文普通话音色SSML调用，方言及小语种音色SSML调用后续会进行支持
使用ssml标签时合成字符不要超过150（包含标签本身），否则出现badcase概率会大大增加

支持的标签
标签

属性

功能

备注

<speak>

根元素。
可设置全局属性。

根元素是必需的。
若无该元素，输入文本将不被认为是SSML

<phoneme>

alphabet="cmu"

指定单词发音的音标
（CMU格式）

alphabet="py"

指定中文词的发音（拼音）

<say-as>

interpret-as

指定解析文本的语义类型
（决定读法）

例如，20可以读作twenty，也可以读作two o

<sub>

alias

文本替换

等价于将其内部文本替换为alias属性中的文本


<speak> 根元素

描述
<speak>作为SSML的根元素出现。不存在该根元素的输入文本不会被认为是SSML。

子元素
任意

注意事项
根元素即包含了其它全部内容的元素，不应存在与之并列或包含根元素的其它元素。
根元素应当只出现一次。

实例
如无特别说明，实例中的音频均由英语UFE前端+DB6音色Tacotron后端生成。

正确示范
<speak>hello world</speak>
错误示范：多次出现
<speak>hello <speak>world</speak></speak>
报错：unrecognized ssml: 1 -- failed to parse child -- failed to parse ssml

错误示范：缺少唯一根元素（存在并列的顶级元素）
<speak>hello</speak> <speak>world</speak>
目前的行为是仅考虑第一个根元素的内容，暂不报错

错误示范：缺少根元素（不被认为是SSML）
hello world
hello <break/> world

<phoneme> 指定字词发音（音素）

描述
<phoneme>用于手动指定部分字词的发音。通常用于纠正TTS为多音字自动生成的不准确发音。

属性
参数

类型

功能

取值

alphabet

enum

指定表示发音（音素）的格式

中文
py拼音
英文
cmu CMU音标格式
ipa柯林斯美音音标
ph

string

指定发音（音素）

不同的alphabet取值对应不同的ph表示方法
参见下文“注意事项”部分

子元素
纯文本

拼音（py）

注意事项
用于中文前端。
使用空格分隔多个拼音。
不区分大小写。
子元素必须为纯文本，且为一个或多个汉字，不应出现标点符号。
声母是可选的。
音调包括：
1 - 阴平、2 - 阳平、3 - 上声、4 - 去声
5 - 轻声
6 - 连续两个上声时，第一个上声的音调即为6（接近2 - 阳平），参见三声变调（连上变调）

实例
<speak>《茜茜公主》是奥地利拍摄的历史题材的德语三部曲电影。</speak>
<speak> 《
    <phoneme alphabet="py" ph="xi1 xi1">茜茜</phoneme>
    公主》是奥地利拍摄的历史题材的德语三部曲电影。
</speak>
<speak>要一起去<phoneme alphabet="py" ph="chi1">吃</phoneme>饭吗</speak>

CMU音标（cmu）

注意事项
用于英文前端。
使用空格分隔多个音素。
不区分大小写。
CMU元音音标包含可选的Stress标号，如IY1、UW2。
子元素必须为纯文本，且为一个或多个英文单词，不应出现标点符号。

实例
正确示范
<speak>
    <!-- 不区分大小写 -->
    <phoneme alphabet="cmu" ph="w uw1 ch IY1 l Uw n">
    Wu Qilong
    </phoneme> 
    and Wu Qilong
</speak>
错误示范：不应出现标点符号
<speak>
    <phoneme alphabet="cmu" ph="w uw1 ch IY1 l Uw n">
    Wu, Qilong
    </phoneme> 
</speak>
报错： should align with the word groups


柯林斯美音音标（ipa）

注意事项
用于英文前端。
不使用分隔符，连续书写音标。
注意只能使用美式音标。
子元素必须为纯文本，且为一个或多个英文单词，不应出现标点符号。
音标包括：
"i",      "ɪ",     "ɛ/e",   "æ",      "ɑ/ɑː", "ɔ/ɔ:",      "u/u:",
"ʊ",      "ʌ",     "ə",     "ɜr/ɜːr", "ər",   "aɪ/ai",     "eɪ/ei",
"ɔɪ/ɔi",  "oʊ/ou", "aʊ/au", "ɑr/ɑːr", "ɔr",   "ʊr/ur/ʊər", "ɛr/ɛər",
"ɪr/ɪər", "p",     "b",     "t",      "d",    "k",         "g",
"f",      "v",     "θ",     "ð",      "s",    "z",         "ʃ",
"ʒ",      "tʃ",    "dʒ",    "tr",     "dr",   "ts",        "dz",
"l",      "r",     "m",     "n",      "ŋ",    "w",         "j",
"h",
重音符和次重音符：
"ˈ", "ˌ"

实例
正确示范
<speak>
    <phoneme alphabet="ipa" ph="wutʃilun">
    Wu Qilong
    </phoneme>
    and Wu Qilong
</speak>

<say-as> 指定字词解析语义（读法）

描述
<say-as>用于指定解析文本的语义类型。同一文本内容可能有不同的解读，也就有不同的读法。

属性
参数

类型

功能

取值

interpret-as

enum

指定语义类型

文本正规化支持的类别（取决于各语言前端的TextNorm模块的能力）
英文
address 地址
cardinal 基数
date 日期
decimal 小数
digit 数字序列
electronic网络
fraction 分数
letters字母序列
letterss字母序列复数
math 数学
measure 度量衡
money金钱
ordinal 序数
plain缩写
score 得分范围
telephone 电话号码
time 时间
verbatim 逐字
中文
Cardinal基数
Cardinal-Liang基数（2 -> 两）
Decimal小数
Abbr缩写
Spell数字序列
Spell-Yao数字序列（1 -> 幺）
Time时间
Time-Duration时间段
Date-Y日期-年
Date-M日期-月
Date-D日期-日
Date-YMD日期-年月（日）
Date-MDY日期-月日（年）
Date-DMY日期-日月（年）
Percent百分数
Fraction分数
Score比分
Currency金钱
Electronic网络
Measure度量衡
Telephone电话
Ordinal序数
Math数学
Range范围
Letters字母序列
Letterss字母序列复数
Verbatim逐字

子元素
纯文本

文本正规化支持的类别

注意事项
不区分大小写。
子元素必须为纯文本。

实例
正确示范
<speak>12:30 and <say-as interpret-as="score">12:30</say-as></speak>
<speak>12.30 and <say-as interpret-as="date">12.30</say-as></speak>
<speak>
    20 
    and <say-as interpret-as="ordinal">20</say-as> 
    and <say-as interpret-as="digit">20</say-as>
</speak>
<speak>hello and <say-as interpret-as="verbatim">hello</say-as></speak>
错误示范：不应出现其它标签
<speak>
    <say-as interpret-as="digit">
        12 <break time="100ms" /> 34
    </say-as>
</speak>
报错： can only contain plain text -- failed to parse child -- failed to parse ssml


<sub> 文本替换

描述
<sub>等价于将其内部的文本替换为其alias属性中的文本。

属性
参数

类型

功能

取值

alias

string

替换文本


实例
<speak><sub alias="语音合成标记语言">SSML</sub></speak>
上一篇
