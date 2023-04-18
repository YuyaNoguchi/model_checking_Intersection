/*distributedのアルゴリズム*/
/*通信は各車両間でのみ行われる*/

#define MIN 0
#define MAX 5
#define IDLE 0
#define WAITING 1
#define PASSING 2
#define VNUM 3  /*車両の台数*/
#define TH 3    /*車両がpreemptionを許す最大回数*/
#define NF 3    /*follow listの最大長*/
/*#define ToPCS 3 交差点を直進して通過する場合の通過時間*/
/*#define ToPCL 4 交差点を左折して通過する場合の通過時間*/

typedef LIST{    /*listのデータ構造*/
    int id[VNUM] = -1;
    byte lane[VNUM] = MAX + 1;
    bool FlgPmpList[VNUM] = false;
}

typedef CHECK{
    bool lane[8] = false;
    int id[8] = -1;
}

mtype = {req, rej, per, fol, emp, ok};    /*チャネルで送受信するメッセージのタイプ　
                                        req:REQUESTメッセージ
                                        rej:REJECTメッセージ
                                        per:PERMITメッセージ
                                        fol:FOLLOWメッセージ
                                        empは誤動作防止用の状態*/


chan ch_global[VNUM] = [VNUM * VNUM] of {mtype, int, byte, int, LIST}; /*各車両が交差点にいるすべての車両にbroadcastするために用いる大域チャンネル*/
int CntGlobal = 0;/*ch_globalを参照するためのカウンタ、配列の末尾の一つ後の要素に設定される*/


hidden mtype h_message;
hidden int h_id_1;
hidden byte h_lane;
hidden int h_id_2;
hidden LIST h_flt;

byte v_counter = 0;

CHECK check;

#define mutex (!((check.lane[0] && check.lane[2]) || (check.lane[0] && check.lane[5]) || (check.lane[0] && check.lane[6]) || (check.lane[0] && check.lane[7]) || (check.lane[1] && check.lane[2]) || (check.lane[1] && check.lane[3]) || (check.lane[1] && check.lane[4]) || (check.lane[1] && check.lane[7]) || (check.lane[2] && check.lane[4]) || (check.lane[2] && check.lane[7]) || (check.lane[3] && check.lane[4]) || (check.lane[3] && check.lane[5]) || (check.lane[3] && check.lane[6]) || (check.lane[4] && check.lane[6]) || (check.lane[5] && check.lane[6]) || (check.lane[5] && check.lane[7])))

/*conflict graphをtableに変換するための処理。入力laneの値にしたがって、conflict = 0,strong concurrent = 1,equal = 2, concurrent = 3のいずれかに値を設定する*/
inline initConflictTable(lane){
    if
    ::  atomic{lane == 0 ->
            conftable[0] = 2;  conftable[1] = 1;  conftable[2] = 0;  conftable[3] = 3;  conftable[4] = 1;  conftable[5] = 0;  conftable[6] = 0;  conftable[7] = 0;}
    ::  atomic{lane == 1 ->
            conftable[0] = 1;  conftable[1] = 2;  conftable[2] = 0;  conftable[3] = 0;  conftable[4] = 0;  conftable[5] = 1;  conftable[6] = 3;  conftable[7] = 0;}
    ::  atomic{lane == 2 ->
            conftable[0] = 0;  conftable[1] = 0;  conftable[2] = 2;  conftable[3] = 1;  conftable[4] = 0;  conftable[5] = 3;  conftable[6] = 1;  conftable[7] = 0;}
    ::  atomic{lane == 3 ->
            conftable[0] = 3;  conftable[1] = 0;  conftable[2] = 1;  conftable[3] = 2;  conftable[4] = 0;  conftable[5] = 0;  conftable[6] = 0;  conftable[7] = 1;}
    ::  atomic{lane == 4 ->
            conftable[0] = 1;  conftable[1] = 0;  conftable[2] = 0;  conftable[3] = 0;  conftable[4] = 2;  conftable[5] = 1;  conftable[6] = 0;  conftable[7] = 3;}
    ::  atomic{lane == 5 ->
            conftable[0] = 0;  conftable[1] = 1;  conftable[2] = 3;  conftable[3] = 0;  conftable[4] = 1;  conftable[5] = 2;  conftable[6] = 0;  conftable[7] = 0;}
    ::  atomic{lane == 6 ->
            conftable[0] = 0;  conftable[1] = 3;  conftable[2] = 1;  conftable[3] = 0;  conftable[4] = 0;  conftable[5] = 0;  conftable[6] = 2;  conftable[7] = 1;}
    ::  atomic{lane == 7 ->
            conftable[0] = 0;  conftable[1] = 0;  conftable[2] = 0;  conftable[3] = 1;  conftable[4] = 3;  conftable[5] = 0;  conftable[6] = 1;  conftable[7] = 2;}
    ::  else ->
        assert(lane < MAX + 1);
    fi;
}

/*メッセージを自分以外の車両に送信する処理。このinlineを用いるときはatomic内で用いるようにする。*/
inline broadcastMessage(CntBroadcast, ch, message, id_1, lane, id_2, flt){
    do
    ::  CntBroadcast < v_counter ->
        if
        :: ch_global[CntBroadcast] == ch ->
                CntBroadcast++;
        :: else ->
                ch_global[CntBroadcast] ! message, id_1, lane, id_2, flt;
                CntBroadcast++;
        fi;
    ::  else->
        CntBroadcast = 0;
        break;
    od;
}

/*各リストに車両を追加する処理*/
inline addVehicleToList(list, Cnt, t_id, t_lane, Flg){
    do
    ::  list.id[Cnt] == -1 ->
            list.id[Cnt] = t_id;
            list.lane[Cnt] = t_lane;
            break;
    ::  else ->
            Cnt++;
    od;
    if
    ::  Flg ->
            list.FlgPmpList[Cnt] = true;
    ::  else ->
    fi;
    Cnt = 0;
}

/*各リストから車両を削除する処理*/
inline deleteVehicleFromList(list, Cnt, t_id){
    do
    ::  list.id[Cnt] == t_id ->
                do
                ::  Cnt == VNUM - 1 ->  /*末尾の場合*/
                        list.id[Cnt] = -1;
                        list.lane[Cnt] = MAX + 1;
                        list.FlgPmpList[Cnt] = false;
                        break;
                ::  else ->
                        list.id[Cnt] = list.id[Cnt + 1];
                        list.lane[Cnt] = list.lane[Cnt + 1];
                        list.FlgPmpList[Cnt] = list.FlgPmpList[Cnt + 1];
                        Cnt++;
                        if
                        ::  list.id[Cnt] == -1 ->
                                break;
                        ::  else ->
                        fi;
                od;
                break;
    ::  list.id[Cnt] == -1 ->   /*削除対象がリストに存在しない場合*/
            break;
    ::  else ->
            Cnt++;
    od;
    Cnt = 0;
}
/*tmtより長く待機したか、permitメッセージを受信したことでpassingになるときの処理*/
inline switchToPassingByPermitOrTmt(st, flt, ll, CntLl, CntFlt, message, t_id, t_lane){
    st = PASSING;
    atomic{
        check.lane[lane] = true;
        check.id[lane] = id;
        /*construct flt*/
        do
        ::  ll.lane[CntLl] == t_lane ->
                if
                ::  CntFlt < NF ->
                        flt.id[CntFlt] = ll.id[CntLl];
                        flt.lane[CntFlt] = ll.lane[CntLl];
                        CntFlt++;
                ::  else ->
                fi;
                CntLl++;
        ::  ll.id[CntLl] == -1 ->
                break;
        ::  else ->
                CntLl++;
        od;
        CntLl = 0;
        CntFlt = 0;
    }
}

/*リストを空にする処理*/
inline emptyList(list, Cnt){
        atomic{
                do
                ::      list.id[Cnt] == -1 ->
                                break;
                ::      else ->
                                list.id[Cnt] = -1;
                                list.lane[Cnt] = 8;
                                list.FlgPmpList[Cnt] = false;
                                Cnt++;
                od;
                Cnt = 0;
        }
}
/*プロセスvehicle: 交差点を通過する車両*/
active [VNUM] proctype vehicle1(){
    /*車両の個別の情報のためのローカル変数の宣言*/
    byte st = IDLE; /*車両のステータス、idle=0,waiting=1,passing=2 */
    int id = -1;  /*プロセスidで車両を区別する */
    byte lane = MIN;    /*所属するレーン番号 */
    byte conftable[8] = 0;    /*conflictやconcurrentを判定するテーブル*/
    bool FlgFollow = false; /*followメッセージによってpassingになったかどうかを判定するフラグ*/
    bool FlgFltLast = false;    /*fltの末尾が自分かどうかを判定するフラグ*/
    bool FlgReject = false; /*rejectメッセージによって待機状態になったことを示すフラグ、passingになるとフラグはfalseになる*/

    /*リストや、カウンタのローカル変数の宣言*/
    LIST hl;
    LIST ll;
    LIST flt;
    byte CntPmp = 0;    /*preemptionが行われた回数を数えるカウンタ*/
    int CntHl = 0;  /*HL参照用のカウンタ*/
    int CntLl = 0;  /*LL参照用のカウンタ*/
    int CntFlt = 0; /*flt参照用のカウンタ*/
    bool FlgPmp = false;    /*preemptionが行われたかどうかを確認するフラグ*/
    bool FlgMes = false;
    byte ok_counter = 0;
    /*メッセージ送受信のために必要なチャネル、変数の宣言*/
    chan ch;
    mtype message = emp;
    mtype temp_message = emp;   /*tempが頭文字の変数はすべてメッセージ受信用の変数*/
    int temp_id_1 = -1;
    byte temp_lane = MAX + 1;
    int temp_id_2 = -1;
    LIST temp_flt;
    int CntBroadcast = 0;/*大域チャンネルを車両から操作するときに必要なカウンタ*/


        
        atomic{    
                /*車両が所属するレーン番号を乱数によって決めるための処理*/
                do
                :: lane < MAX -> lane++;
                :: break;
                od;
        }

        /*車両が所属するレーンに対してcoflictかどうかを判断する配列を設定する*/
        initConflictTable(lane);
        /*CoBegin*/
        /*On entering the monitoring area:*/
        atomic{
                id = v_counter;
                ch = ch_global[v_counter];
                st = WAITING;
                message = req;
                printf("start:%d,lane:%d\n", id, lane);
                printf("send request:%d\n", id);
                broadcastMessage(CntBroadcast, ch, message, id, lane, -1, flt);
                v_counter++;
        }
        
        do
        ::  atomic{ch ? temp_message, temp_id_1, temp_lane, temp_id_2, temp_flt -> FlgMes = true;}
                if
                ::  temp_message == req ->  /*On receiving REQUEST message*/
                        atomic{
                                printf("receive request:%d from %d\n", id, temp_id_1);
                                if
                                ::  st > IDLE ->    /*(st == WAITING) || (st ==PASSING)と同意*/
                                        if
                                        ::  (lane == temp_lane) || (conftable[temp_lane] == 0) ->
                                                /*CntPmpがTHを超えていないかどうかを調べる*/
                                                if
                                                ::  CntPmp < TH ->
                                                        /*HLの中にtemp_id_1とstrong concurrentな関係の車両が存在するか調べる*/
                                                        do
                                                        ::  hl.id[CntHl] == -1 ->   /*リストの末尾の一つ後ろならばカウンターを初期化して、rejectをbroadcastする*/
                                                                atomic{
                                                                        CntHl = 0;
                                                                        addVehicleToList(ll, CntLl, temp_id_1, temp_lane, FlgPmp);
                                                                        message = rej;
                                                                        printf("send reject1:%d\n", id);
                                                                        broadcastMessage(CntBroadcast, ch, message, id, lane, temp_id_1, flt);
                                                                }
                                                                break;
                                                        ::  else ->
                                                                if
                                                                ::  conftable[hl.lane[CntHl]] == 1 ->
                                                                        atomic{
                                                                                FlgPmp = true;
                                                                                addVehicleToList(hl, CntHl, temp_id_1, temp_lane, FlgPmp);
                                                                                FlgPmp = false;
                                                                                CntPmp++;
                                                                        }
                                                                        break;
                                                                ::  else ->
                                                                        CntHl++;
                                                                fi;
                                                        od;
                                                ::  else ->
                                                        atomic{
                                                                addVehicleToList(ll, CntLl, temp_id_1, temp_lane, FlgPmp);
                                                                message = rej;
                                                                printf("send reject2:%d\n", id);
                                                                broadcastMessage(CntBroadcast, ch, message, id, lane, temp_id_1, flt);
                                                        }
                                                fi;
                                        ::  else ->
                                                atomic{
                                                        message = ok;
                                                        printf("send ok:%d\n", id);
                                                        broadcastMessage(CntBroadcast, ch, message, id, lane, temp_id_1, flt);
                                                }
                                        fi;
                                ::  else ->
                                fi;
                        }
                ::  temp_message == rej ->  /*On receiving REJECT message*/
                        printf("receive reject:%d from %d\n", id, temp_id_1);
                        if
                        ::  st == WAITING ->
                                if
                                ::  id == temp_id_2 ->  /*rejectの対象が自分だったならば*/
                                        atomic{
                                                addVehicleToList(hl, CntHl, temp_id_1, temp_lane, FlgPmp);
                                                FlgReject = true;
                                        }
                                ::  else ->
                                        do
                                        ::  hl.id[CntHl] == -1 ->
                                                CntHl = 0;
                                                break;
                                        ::  hl.id[CntHl] == temp_id_2 ->    /*rejectの対象がHLに含まれているならば*/
                                                if
                                                ::  hl.FlgPmpList[CntHl] -> /*preemptionがおこなわれていたならば*/
                                                        if
                                                        ::  conftable[temp_lane] == 0 ->
                                                                CntHl = 0;
                                                                do
                                                                ::  hl.id[CntHl] == temp_id_1 ->    /*rejectを発信した車両がHLに含まれているならば*/
                                                                        break;
                                                                ::  hl.id[CntHl] == -1 ->   /*rejectを発信した車両がHLに含まれていないならば*/
                                                                        CntHl = 0;
                                                                        atomic{
                                                                                deleteVehicleFromList(hl, CntHl, temp_id_2);
                                                                                message = rej;
                                                                                printf("send reject3:%d\n", id);
                                                                                broadcastMessage(CntBroadcast, ch, message, id, lane, temp_id_2, flt);
                                                                        }
                                                                ::  else ->
                                                                        CntHl++;
                                                                od;
                                                                CntHl = 0;
                                                        ::  conftable[temp_lane] == 1 ->
                                                                atomic{
                                                                        deleteVehicleFromList(hl, CntHl, temp_id_2);
                                                                        message = rej;
                                                                        printf("send reject4:%d\n", id);
                                                                        broadcastMessage(CntBroadcast, ch, message, id, lane, temp_id_2, flt);
                                                                }
                                                        ::  else ->
                                                        fi;
                                                ::  else ->
                                                fi;
                                                break;
                                        ::  else ->
                                                CntHl++;
                                        od;
                                fi;
                        ::  else ->
                        fi;
                ::  temp_message == per ->  /*On receiving PERMIT message or tmt occurs*/
                        printf("receive permit:%d from %d\n", id, temp_id_1);
                        deleteVehicleFromList(hl, CntHl, temp_id_1);
                        if
                        ::  hl.id[0] == -1 ->   /*HLの中身が空ならば*/
                                switchToPassingByPermitOrTmt(st, flt, ll, CntLl, CntFlt, message, id, lane);
                                atomic{
                                        message = fol;
                                        printf("send follow1:%d\n", id);
                                        broadcastMessage(CntBroadcast, ch, message, id, lane, -1, flt);
                                }
                        ::  else ->
                        fi;
                ::  temp_message == fol ->  /*On receiving FOLLOW message*/
                        printf("receive follow:%d from %d\n", id, temp_id_1);
                        do
                        ::  temp_flt.id[CntFlt] == id ->
                                emptyList(hl, CntHl);
                                atomic{
                                        st = PASSING;
                                        FlgFollow = true;
                                        check.lane[lane] = true;
                                        check.id[lane] = id;
                                }
                                CntFlt++;
                                if
                                ::  temp_flt.id[CntFlt] == -1 ->
                                        FlgFltLast = true;
                                ::  else ->
                                fi;
                                break;
                        ::  temp_flt.id[CntFlt] == -1 ->
                                break;
                        ::  else ->
                                CntFlt++;
                        od;
                        CntFlt = 0;
                        if
                        ::  !FlgFollow ->
                                if
                                ::  conftable[temp_lane] == 0 ->
                                        deleteVehicleFromList(hl, CntHl, temp_id_1);
                                        do
                                        ::  temp_flt.id[CntFlt] == -1 -> printf("check1:%d\n",id);
                                                if
                                                ::  CntFlt > 0 ->
                                                        addVehicleToList(hl, CntHl, temp_flt.id[CntFlt - 1], temp_flt.lane[CntFlt - 1], FlgPmp);
                                                ::  else ->
                                                fi;
                                                break;
                                        ::  else -> printf("check2:%d\n",id);
                                                deleteVehicleFromList(hl, CntHl, temp_flt.id[CntFlt]);
                                                deleteVehicleFromList(ll, CntLl, temp_flt.id[CntFlt]);
                                                CntFlt++;
                                        od;
                                ::  else ->
                                fi;
                        ::  else ->
                        fi;
                :: temp_message == ok ->
                        printf("receive ok to %d:%d from %d\n", temp_id_2, id, temp_id_1);
                        if
                        :: temp_id_2 == id ->
                                ok_counter++;
                        :: else ->
                        fi;
                fi;
        ::  (!FlgReject && (st == WAITING)) ->
                        if
                        :: ((v_counter < 2) && (empty(ch))) || ((ok_counter >= v_counter - 1) && (FlgMes) && (empty(ch))) ->
                                printf("empty!:%d\n", id);
                                switchToPassingByPermitOrTmt(st, flt, ll, CntLl, CntFlt, message, id, lane);
                                atomic{
                                        message = fol;
                                        printf("send follow2:%d\n", id);
                                        broadcastMessage(CntBroadcast, ch, message, id, lane, -1, flt);
                                }
                        :: atomic{else -> printf("not enter!:%d\n",id);}
                        fi;
        ::  st == PASSING ->
                        break;
        od;
        /*On exiting the intersection*/
        atomic{
                st = IDLE;
                /*v_counter--;*/
                if
                        :: check.id[lane] == id ->
                                check.lane[lane] = false;
                                check.id[lane] = -1;
                        :: else ->/*何もしない*/
                fi;
        }
        if
        ::  FlgFollow && FlgFltLast ->
                atomic{
                        message = per;
                        printf("send permit:%d\n", id);
                        broadcastMessage(CntBroadcast, ch, message, id, 8, -1, flt);
                }
        ::  else ->
        fi;
        printf("end!:%d\n", id);
}

