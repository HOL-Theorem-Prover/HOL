structure bsubstML :> bsubstML =
struct
  nonfix empty_memory MEM_ITEMS MEM_WRITE_BLOCK MEM_WRITE MEM_WRITE_WORD
         MEM_WRITE_BYTE MEM_READ SET_BYTE ADDR30 ::- :- * / div mod + -
         ^ @ <> > < >= <= := o before;
  
  open numML fcpML wordsML;
  type mem = (word30, word32) Redblackmap.dict
  val mem_updates = ref ([]: word30 list)
  fun :- a b = fn m => fn c => if a = c then b else m c
    
  fun ::- a l =
        fn m => fn b =>
        if word_ls a b andalso < (- (w2n b) (w2n a)) (listML.LENGTH l)
          then listML.EL (- (w2n b) (w2n a)) l else m b
    
  fun ADDR30 addr =
        word_extract_itself (Tyop ("i30", [])) (fromString"31") TWO addr
    
  fun SET_BYTE oareg b w =
        word_modify (fn i => fn x =>
          < i (fromString"8")
          andalso
          (if word_eq oareg (n2w_itself (ZERO,(Tyop ("i2", []))))
             then index b i else x)
          orelse
          ((<= (fromString"8") i andalso < i (fromString"16"))
           andalso
           (if word_eq oareg (n2w_itself (ONE,(Tyop ("i2", []))))
              then index b (- i (fromString"8")) else x)
           orelse
           ((<= (fromString"16") i andalso < i (fromString"24"))
            andalso
            (if word_eq oareg (n2w_itself (TWO,(Tyop ("i2", []))))
               then index b (- i (fromString"16")) else x)
            orelse
            (<= (fromString"24") i andalso < i (fromString"32"))
            andalso
            (if word_eq oareg
                  (n2w_itself ((fromString"3"),(Tyop ("i2", []))))
               then index b (- i (fromString"24")) else x)))) w
    
  fun fromHexNum s n =
        wordsML.fromNum(numML.fromHexString n, fcpML.Tyop (s, []));

  val fromNum32 = (fromHexNum "i32"): string -> word32;

  fun MEM_READ(m,a) = Redblackmap.find(m, a)
                       handle NotFound => fromNum32 "E6000010";
    
  fun MEM_WRITE_BYTE mem addr word =
        let val addr30 = ADDR30 addr
        in
           Redblackmap.insert(mem, (addr30: word30),
             SET_BYTE
                (word_extract_itself (Tyop ("i2", [])) ONE ZERO addr)
                (word_extract_itself (Tyop ("i8", [])) (fromString"7")
                   ZERO word) (MEM_READ(mem,addr30)))
        end

  fun MEM_WRITE_WORD (mem:mem) addr word =
        Redblackmap.insert(mem,ADDR30 addr,word)

  fun MEM_WRITE b m a =
        (:= (mem_updates, ADDR30 a :: !mem_updates);
          if b then MEM_WRITE_BYTE m a else MEM_WRITE_WORD m a)

  fun MEM_WRITE_BLOCK m (a: word30) [] = m
    | MEM_WRITE_BLOCK m a (d::l) =
       (:= (mem_updates, ADDR30 a :: !mem_updates);
        MEM_WRITE_BLOCK (Redblackmap.insert(m, a, (d: word32)))
          (word_add a (n2w_itself (ONE,(Tyop ("i30", []))))) l)
    
  fun MEM_ITEMS (m:mem) = Redblackmap.listItems m

  fun word_compare(v, w) =
    let val m = w2n v and n = w2n w in
      if m = n then
        EQUAL
      else
        if < m n then LESS else GREATER
    end

  val empty_memory = (Redblackmap.mkDict word_compare):mem
end
