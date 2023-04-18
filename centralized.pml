/*centralizedのアルゴリズム*/
/*通信のやり取りは車両と制御システム間のみでメッセージの損失はないものとする*/
#define MIN 0
#define MAX 7
#define VNUM 4 /*車両の台数*/
#define NP 8    /*passing listに含めることができる最大の台数*/

typedef PLT{    /*passing listのデータ構造*/
    int list[NP] = -1;
}
typedef LSL{    /*lockをかけるテーブルのためのデータ構造*/
    byte list[3];
}
typedef RP{     /*pending request listのデータ構造*/
    int list[VNUM] = -1;
    byte lane[VNUM] = 8;
}
typedef CHECK{
    bool lane[8] = false;
    int id[8] = -1;
}

mtype = {req, rel, setup, emp};    /*チャネルで送受信するメッセージのタイプ　reqがREQUESTメッセージに、relがRELEASEメッセージに対応する　empは誤動作防止用の状態*/

chan v_to_c = [VNUM*2] of {int, byte, mtype}; /*車両からコントローラーへのメッセージを受け取るチャネル　メッセージの最大数は車両の最大数と同じ数*/

/*メッセージ受信のために必要なチャネル*/
chan c_to_v[VNUM] = [VNUM] of {PLT, int};

CHECK check;    /*observerが監視する変数*/

 PLT h_plt;
 int h_id;
 chan h_ch;

 int ch_counter = 0;

#define mutex (!((check.lane[0] && check.lane[2]) || (check.lane[0] && check.lane[5]) || (check.lane[0] && check.lane[6]) || (check.lane[0] && check.lane[7]) || (check.lane[1] && check.lane[2]) || (check.lane[1] && check.lane[3]) || (check.lane[1] && check.lane[4]) || (check.lane[1] && check.lane[7]) || (check.lane[2] && check.lane[4]) || (check.lane[2] && check.lane[7]) || (check.lane[3] && check.lane[4]) || (check.lane[3] && check.lane[5]) || (check.lane[3] && check.lane[6]) || (check.lane[4] && check.lane[6]) || (check.lane[5] && check.lane[6]) || (check.lane[5] && check.lane[7])))

/*プロセスvehicle: 交差点を通過する車両*/
active [VNUM] proctype vehicle(){
    /*車両の個別の情報のためのローカル変数の宣言*/
    byte st = 0;/*車両のステータス、idle=0,waiting=1,passing=2 */

    int id = -1;/*プロセスidで車両を区別する */

    atomic{
        id = ch_counter;
        ch_counter++;
    }

    byte l_number = MIN;/*所属するレーン番号 */

    /*メッセージ受信や、カウンタに必要なローカル変数の宣言*/
    PLT plt;/*passingになれる車両のidが入るリスト*/
    int last = -1;/*pltの最後尾の車両のid*/
    int i = 0;/*pltの中身を確認するためのカウンター*/


    /*v_to_c ! -1, 8, setup, c_to_v;    /*変更点*/
    
        atomic {    /*車両が所属するレーン番号を乱数によって決めるための処理*/
            do
            :: l_number < MAX -> l_number++;
            ::  break;
            od;
        }

        /*controllerにREQUESTメッセージを送信 */
        v_to_c ! id, l_number, req;     /*変更点*/
        
        st = 1;/*状態をwaitingに変更 */
        
        /*PERMITメッセージが来るまで待機する*/
        do
        :: st == 1 -> printf("%d:start\n", id)
            if  
            :: c_to_v[id] ? plt, last  -> printf("%d:get message\n", id)    /*pltに自分のidが入っているかどうかを調べ、ある場合は状態をpassingに変更してループを抜ける*/    /*変更点*/
                do
                :: plt.list[i] == id -> 
                    atomic{
                        st = 2; /*状態をpassingに変更*/
                        check.lane[l_number] = true;
                        check.id[l_number] = id;
                    }
                    break;
                :: else ->  /*pltの次の要素を参照するために、カウンタを1進める*/
                    i++;
                    if
                    :: i == NP ->   /*送信されたpltのすべての要素の参照が終わった場合、もう一度メッセージの受信待ち状態に戻る*/
                        i = 0;
                        printf("%d:not exist!\n", id);
                        break;
                    :: else -> /*何もしない*/
                    fi;
                od;
            fi;
        :: st == 2 -> printf("%d:in\n", id);
            i = 0;
            break;
        od;
        /*pltの最後尾が自分のidだった場合はcontrollerにRELEASEメッセージを送信する */
        if
        :: last == id -> v_to_c ! id, l_number, rel;   
        :: else -> /*何もしない*/
        fi;
    
        st = 0; /*状態をidleに変更*/
        printf("%d:out\n", id)
        if
        :: check.id[l_number] == id ->
            check.lane[l_number] = false;
            check.id[l_number] = -1;
        :: else ->/*何もしない*/
        fi;
}


/*コントローラーから車両へ送信するメッセージが入るチャネルに、すでにメッセージが入っているかどうか調べ、入っている場合はチャネルを空にする手続き　コントローラーがメッセージを送信する直前に実行される*/
/*inline checkCtoV(c_to_v, plt, id){
    atomic{
        if
        :: full(c_to_v) -> c_to_v ? plt, id;
            assert(empty(c_to_v));
        :: empty(c_to_v) ->
        fi;
    }
}*/

/*pending listに車両を追加する手続き　REQUESTメッセージを受信した後、pltを送信しなかった場合に実行される*/
inline addToRp(rp, r_counter, v_id, v_l_number){
    atomic{
        do  /*rpが空の位置までr_counterを進める*/
        :: rp.list[r_counter] == -1 -> 
            break;
        :: else ->
            r_counter++;
        od;
        rp.list[r_counter] = v_id;
        rp.lane[r_counter] = v_l_number;
        r_counter = 0;
    }
}

/*pending listに含まれている車両を削除する手続き　pendinglistからpassing listに車両を追加した直後に実行される*/
inline reduceRp(tempRc, r_counter, rp){
    atomic{
        tempRc = r_counter;
        do
        /*rpの要素をひとつ前にずらし、rpを縮小する */
        :: rp.list[tempRc] == -1 ->
            break;
        :: tempRc == VNUM - 1 ->
            rp.list[tempRc] = -1;
            rp.lane[tempRc] = 8;
            break;
        :: else ->
            rp.list[tempRc] = rp.list[tempRc + 1];
            rp.lane[tempRc] = rp.lane[tempRc + 1];
            tempRc++;
        od;
    }
}

inline reducePlt(i, j, plt, p_counter, v_id){
    atomic{
        i = 0;
        j = 0;
        do
        :: v_id == plt.list[j] ->
            j++;
            do
            :: j < p_counter ->
                plt.list[i] = plt.list[j];
                i++;
                j++;
            :: else ->
                do
                :: p_counter > i ->
                    p_counter--;
                    plt.list[p_counter] = -1;
                :: else ->
                    break;
                od;
                break;
            od;
            break;
        :: else ->
            j++;
            if
            :: j == NP ->
                break;
            :: else ->
                /*何もしない*/
            fi;
        od;
        i = 0;
    }
}

/*lslに対応するロックをlockにして、pending listからpass listを再構成する手続き　REQUESTメッセージを受信したときのcase2とRELEASEメッセージを受信て特定の場合のときに実行される*/

/*プロセスcontroller: 制御システム*/
 active proctype controller(){

     /*送信先のチャネルを保管するリスト*/
    chan temp_ch = [1] of {PLT, int};

    
    int v_id = -1;/*メッセージを送信してきた車両のid*/
    byte v_l_number = 8;/*メッセージを送信してきた車両が所属するレーンの番号*/
    mtype message = emp;/*REQUESTかRELEASEかのメッセージ　初期値は誤作動を起こさないようにemp*/
    PLT plt;/*passingになれる車両のidが入るリスト*/
    int p_counter = 0;/*pltの参照に使用するカウンタ*/
    RP rp;/*pending listのためのリスト*/
    int r_counter = 0;/*rpの参照に使用するカウンタ*/
    LSL lsl[8];/*lockをかけるレーン番号の対応表*/
    /*lslの設定*/
    atomic{
        lsl[0].list[0] = 6;
        lsl[0].list[1] = 7;
        lsl[0].list[2] = 0;
        lsl[1].list[0] = 1;
        lsl[1].list[1] = 2;
        lsl[1].list[2] = 3;
        lsl[2].list[0] = 0;
        lsl[2].list[1] = 1;
        lsl[2].list[2] = 2;
        lsl[3].list[0] = 3;
        lsl[3].list[1] = 4;
        lsl[3].list[2] = 5;
        lsl[4].list[0] = 2;
        lsl[4].list[1] = 3;
        lsl[4].list[2] = 4;
        lsl[5].list[0] = 5;
        lsl[5].list[1] = 6;
        lsl[5].list[2] = 7;
        lsl[6].list[0] = 4;
        lsl[6].list[1] = 5;
        lsl[6].list[2] = 6;
        lsl[7].list[0] = 7;
        lsl[7].list[1] = 0;
        lsl[7].list[2] = 1;
    }
    bool lock[8] = false;/*各レーンのロック　falseでunlock、trueでlockの状態を表す　初期値はすべてunlockのためfalse*/
    byte latest[8] = 8;/*各レーンを最後にロックした車両のレーン番号を保存するリスト */
    int temp = 0;/*r_counterを一時的に保存する変数*/
    int i = 0;/*リスト操作のためのカウンタ*/
    int j = 0;/*リスト操作のためのカウンタ*/
    
    /*メッセージを受け取る無限ループ */
    endcontroller:
    do
    :: v_to_c ? v_id, v_l_number, message ->
        if
        /*REQUESTを受信した場合 */
        :: atomic{message == req -> 
            message = emp;
            }
            /*メッセージを送信してきた車両のレーンに対応するロックの状態によって、処理が分岐 */
            if
            :: lock[lsl[v_l_number].list[0]] == true && lock[lsl[v_l_number].list[1]] == true && lock[lsl[v_l_number].list[2]] == true ->   /*lslに対応するレーン番号のロックがすべてlockの場合*/
                if
                :: latest[lsl[v_l_number].list[0]] == v_l_number && latest[lsl[v_l_number].list[1]] == v_l_number && latest[lsl[v_l_number].list[2]] == v_l_number ->/*さらに、そのlockをかけた車両のレーン番号がすべてメッセージを送信した車両と同じ場合*/
                    
                    if
                    :: p_counter < NP ->    /*pltが埋まり切っていないため、pltに車両を追加することが可能である*/
                        plt.list[p_counter] = v_id; /*pltにメッセージを送信してきた車両を追加する*/
                        atomic{
                            do
                            ::  i < ch_counter ->
                                /*checkCtoV(c_to_v[i], h_plt, h_id);  /*c_to_vが空かどうかを確認する*/   /*変更点*/
                                c_to_v[i] ! plt, v_id;
                                i++;
                            ::  else ->
                                break;
                            od;
                            i = 0;
                        }
                        p_counter++;    /*pltを参照する位置を1進める*/
                    :: else ->
                        addToRp(rp, r_counter, v_id, v_l_number);
                    fi;
                :: else ->
                    addToRp(rp, r_counter, v_id, v_l_number);
                fi;
            :: lock[lsl[v_l_number].list[0]] == false && lock[lsl[v_l_number].list[1]] == false && lock[lsl[v_l_number].list[2]] == false ->    /*lslに対応するレーン番号のロックがすべてunlockの場合*/
                lock[lsl[v_l_number].list[0]] = true; lock[lsl[v_l_number].list[1]] = true; lock[lsl[v_l_number].list[2]] = true;   /*lslに対応するロックをすべてlockにする*/
                latest[lsl[v_l_number].list[0]] = v_l_number; latest[lsl[v_l_number].list[1]] = v_l_number; latest[lsl[v_l_number].list[2]] = v_l_number;   /*最後にlockにした車両の所属するレーン番号を更新する*/
                /*メッセージを送信した車両と同じレーン上に存在し、pending listに含まれている車両をpltに加える*/
                do  /*rpの中身をすべて調べる*/
                :: rp.list[r_counter] == -1 ->  /*rpの中身がすべて埋まっておらず、最後尾の一つ後ろを参照したためにループを抜ける場合*/
                    r_counter = 0;
                    break;
                :: r_counter >= VNUM -> /*rpの中身がすべて埋まっており、最後尾を参照し終わったためにループを抜ける場合*/
                    r_counter = 0;
                    break;
                :: else ->
                    if
                    :: p_counter < NP ->    /*pltがすべて埋まっていなければ、追加処理を行う*/
                        if
                        :: rp.lane[r_counter] == v_l_number ->  /*rpに含まれる車両の所属するレーン番号がメッセージを送信してきた車両と同じである場合*/
                            plt.list[p_counter] = rp.list[r_counter];
                            p_counter++;
                            reduceRp(temp, r_counter, rp);
                        :: else -> 
                            r_counter++;
                        fi;
                    :: else ->  /*pltがすべて埋まっていればrpを一つずつ進める処理をループを抜けるまで続ける*/
                        r_counter++;
                    fi;
                od;
                /*メッセージを送信した車両を最後にpltに加える */
                if
                :: p_counter < NP ->
                    plt.list[p_counter] = v_id;
                    atomic{
                        do
                        ::  i < ch_counter ->
                            /*checkCtoV(c_to_v[i], h_plt, h_id);  /*c_to_vが空かどうかを確認する*/   /*変更点*/
                            c_to_v[i] ! plt, v_id;
                            i++;
                        ::  else ->
                            break;
                        od;
                        i = 0;
                    }
                    p_counter++;
                :: else ->
                    addToRp(rp, r_counter, v_id, v_l_number);
                fi;
            :: else ->
                addToRp(rp, r_counter, v_id, v_l_number);
            fi;
        /*RELEASEを受信した場合 */
        /*メッセージを送信した車両がlatestに対応するロックすべてを解放する */
        :: atomic{message == rel -> 
                message = emp;
            }
            /*メッセージを送信した車両が所属しているレーンがかけたロックをすべて解除する */
            atomic{
                i = 0;
                do
                :: i < 8 ->
                    if
                    :: latest[i] == v_l_number ->
                        lock[i] = false;
                    :: else -> /*何もしない*/
                    fi;
                    i++;
                :: else ->
                    break;
                od;
            }
            
            reducePlt(i, j, plt, p_counter, v_id);
            /*pending listに入っている車両について、その車両が所属するレーンのlslがすべてアンロックならばpltに加えてpermitを送信する */
            do
            :: rp.list[r_counter] == -1 ->
                r_counter = 0;
                break;
            :: r_counter >= VNUM ->
                r_counter = 0;
                break;
            :: else ->
                if
                :: p_counter < NP ->
                    if
                    :: lock[lsl[rp.lane[r_counter]].list[0]] == false && lock[lsl[rp.lane[r_counter]].list[1]] == false && lock[lsl[rp.lane[r_counter]].list[2]] == false ->
                        lock[lsl[rp.lane[r_counter]].list[0]] = true; lock[lsl[rp.lane[r_counter]].list[1]] = true; lock[lsl[rp.lane[r_counter]].list[2]] = true;   /*その車両が所属するレーンに対応するロックを閉じる*/
                        latest[lsl[rp.lane[r_counter]].list[0]] = rp.lane[r_counter]; latest[lsl[rp.lane[r_counter]].list[1]] = rp.lane[r_counter]; latest[lsl[rp.lane[r_counter]].list[2]] = rp.lane[r_counter];
                        plt.list[p_counter] = rp.list[r_counter];
                        p_counter++;
                        reduceRp(temp, r_counter, rp);
                        temp = r_counter;
                        /*pending list中に同様のレーン番号を持つ車両があればpltに加える*/
                        do
                        :: rp.list[temp] == -1 ->
                            break;
                        :: temp >= VNUM ->
                            break;
                        :: else ->
                            if
                            :: p_counter < NP ->
                                if
                                :: rp.lane[temp] == v_l_number ->
                                    plt.list[p_counter] = rp.list[temp];
                                    p_counter++;
                                    int temp2;
                                    reduceRp(temp2, temp, rp);
                                :: else ->
                                    temp++;
                                fi;
                            :: else ->
                                temp++;
                            fi;
                        od;
                        /*pltの最後尾の車両をv_idに入れて、pltの最後尾の車両とする */
                        v_id = plt.list[p_counter - 1];
                        atomic{
                            do
                            ::  i < ch_counter ->
                                /*checkCtoV(c_to_v[i], h_plt, h_id);  /*c_to_vが空かどうかを確認する*/   /*変更点*/
                                c_to_v[i] ! plt, v_id;
                                i++;
                            ::  else ->
                                break;
                            od;
                            i = 0;
                        }
                        r_counter++;
                    :: else ->
                        r_counter++;
                    fi;
                :: else ->
                    r_counter++;
                    break;
                fi;
            od;
        fi;
     od;
 }
