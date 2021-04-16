extern void abort(void);

extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "bubble_sort-2.c", 3, __extension__ __PRETTY_FUNCTION__); })); }


extern void __assert_fail (__const char *__assertion, __const char *__file,
      unsigned int __line, __const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, __const char *__file,
      unsigned int __line,
      __const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

typedef unsigned int size_t;




struct list_head {
   struct list_head *next ;
   struct list_head *prev ;
};
struct node {
   int value ;
   struct list_head linkage ;
   struct list_head nested ;
};
extern __attribute__((__nothrow__)) void *malloc(size_t __size ) __attribute__((__malloc__)) ;
extern __attribute__((__nothrow__)) void free(void *__ptr ) ;
extern __attribute__((__nothrow__, __noreturn__)) void abort(void) ;
extern int __VERIFIER_nondet_int(void);
static void fail(void)
{
  {
  ERROR: {reach_error();abort();}((0) ? (void) (0) : __assert_fail ("0", "test-0180.c", 11, __PRETTY_FUNCTION__));
  goto ERROR;
}
}


struct list_head gl_list = {& gl_list, & gl_list};

static void inspect(struct list_head const *head )
{ struct node const *node ;
  unsigned int __cil_tmp3 ;
  struct list_head *__cil_tmp4 ;
  unsigned int __cil_tmp5 ;
  int __cil_tmp6 ;
  unsigned int __cil_tmp7 ;
  unsigned int __cil_tmp8 ;
  unsigned int __cil_tmp9 ;
  struct list_head *__cil_tmp10 ;
  unsigned int __cil_tmp11 ;
  int __cil_tmp12 ;
  unsigned int __cil_tmp13 ;
  unsigned int __cil_tmp14 ;
  struct list_head *__cil_tmp15 ;
  unsigned int __cil_tmp16 ;
  struct list_head *__cil_tmp17 ;
  unsigned int __cil_tmp18 ;
  int __cil_tmp19 ;
  unsigned int __cil_tmp20 ;
  unsigned int __cil_tmp21 ;
  unsigned int __cil_tmp22 ;
  struct list_head *__cil_tmp23 ;
  unsigned int __cil_tmp24 ;
  int __cil_tmp25 ;
  struct node *__cil_tmp26 ;
  unsigned int __cil_tmp27 ;
  unsigned int __cil_tmp28 ;
  struct list_head *__cil_tmp29 ;
  unsigned long __cil_tmp30 ;
  char *__cil_tmp31 ;
  char *__cil_tmp32 ;
  struct node *__cil_tmp33 ;
  unsigned int __cil_tmp34 ;
  unsigned int __cil_tmp35 ;
  struct list_head const *__cil_tmp36 ;
  unsigned int __cil_tmp37 ;
  unsigned int __cil_tmp38 ;
  unsigned int __cil_tmp39 ;
  struct list_head *__cil_tmp40 ;
  unsigned int __cil_tmp41 ;
  int __cil_tmp42 ;
  unsigned int __cil_tmp43 ;
  unsigned int __cil_tmp44 ;
  struct list_head const *__cil_tmp45 ;
  unsigned int __cil_tmp46 ;
  unsigned int __cil_tmp47 ;
  unsigned int __cil_tmp48 ;
  unsigned int __cil_tmp49 ;
  struct list_head *__cil_tmp50 ;
  unsigned int __cil_tmp51 ;
  int __cil_tmp52 ;
  unsigned int __cil_tmp53 ;
  unsigned int __cil_tmp54 ;
  struct list_head const *__cil_tmp55 ;
  unsigned int __cil_tmp56 ;
  unsigned int __cil_tmp57 ;
  unsigned int __cil_tmp58 ;
  struct list_head *__cil_tmp59 ;
  unsigned int __cil_tmp60 ;
  int __cil_tmp61 ;
  unsigned int __cil_tmp62 ;
  unsigned int __cil_tmp63 ;
  struct list_head const *__cil_tmp64 ;
  unsigned int __cil_tmp65 ;
  unsigned int __cil_tmp66 ;
  unsigned int __cil_tmp67 ;
  unsigned int __cil_tmp68 ;
  struct list_head *__cil_tmp69 ;
  unsigned int __cil_tmp70 ;
  int __cil_tmp71 ;
  struct node const *__cil_tmp72 ;
  unsigned int __cil_tmp73 ;
  unsigned int __cil_tmp74 ;
  int __cil_tmp75 ;
  unsigned int __cil_tmp76 ;
  unsigned int __cil_tmp77 ;
  struct list_head const *__cil_tmp78 ;
  struct node const *__cil_tmp79 ;
  unsigned int __cil_tmp80 ;
  unsigned int __cil_tmp81 ;
  int __cil_tmp82 ;
  int const *__cil_tmp83 ;
  struct node const *__cil_tmp84 ;
  unsigned int __cil_tmp85 ;
  unsigned int __cil_tmp86 ;
  int __cil_tmp87 ;
  unsigned int __cil_tmp88 ;
  unsigned int __cil_tmp89 ;
  struct list_head *__cil_tmp90 ;
  unsigned int __cil_tmp91 ;
  unsigned int __cil_tmp92 ;
  struct list_head *__cil_tmp93 ;
  unsigned int __cil_tmp94 ;
  unsigned int __cil_tmp95 ;
  int __cil_tmp96 ;
  unsigned int __cil_tmp97 ;
  unsigned int __cil_tmp98 ;
  unsigned int __cil_tmp99 ;
  struct list_head *__cil_tmp100 ;
  struct list_head *__cil_tmp101 ;
  unsigned int __cil_tmp102 ;
  unsigned int __cil_tmp103 ;
  int __cil_tmp104 ;
  struct list_head *__cil_tmp105 ;
  unsigned int __cil_tmp106 ;
  unsigned int __cil_tmp107 ;
  unsigned int __cil_tmp108 ;
  struct list_head const *__cil_tmp109 ;
  unsigned int __cil_tmp110 ;
  struct list_head *__cil_tmp111 ;
  unsigned int __cil_tmp112 ;
  struct node *__cil_tmp113 ;
  unsigned int __cil_tmp114 ;
  unsigned int __cil_tmp115 ;
  struct list_head *__cil_tmp116 ;
  unsigned long __cil_tmp117 ;
  char *__cil_tmp118 ;
  char *__cil_tmp119 ;
  struct node *__cil_tmp120 ;
  unsigned int __cil_tmp121 ;
  int __cil_tmp122 ;

  {
  {
  while (1) {
    while_0_continue: ;
    if (! head) {
      {
      fail();
      }
    } else {
    }
    goto while_0_break;
  }
  while_0_break: ;
  }
  {
  while (1) {
    while_1_continue: ;
    {
    __cil_tmp3 = (unsigned int )head;
    __cil_tmp4 = *((struct list_head * const *)head);
    __cil_tmp5 = (unsigned int )__cil_tmp4;
    __cil_tmp6 = __cil_tmp5 != __cil_tmp3;
    if (! __cil_tmp6) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_1_break;
  }
  while_1_break: ;
  }
  {
  while (1) {
    while_2_continue: ;
    {
    __cil_tmp7 = (unsigned int )head;
    __cil_tmp8 = (unsigned int )head;
    __cil_tmp9 = __cil_tmp8 + 4;
    __cil_tmp10 = *((struct list_head * const *)__cil_tmp9);
    __cil_tmp11 = (unsigned int )__cil_tmp10;
    __cil_tmp12 = __cil_tmp11 != __cil_tmp7;
    if (! __cil_tmp12) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_2_break;
  }
  while_2_break: ;
  }
  __cil_tmp13 = (unsigned int )head;
  __cil_tmp14 = __cil_tmp13 + 4;
  __cil_tmp15 = *((struct list_head * const *)__cil_tmp14);
  head = (struct list_head const *)__cil_tmp15;
  {
  while (1) {
    while_3_continue: ;
    if (! head) {
      {
      fail();
      }
    } else {
    }
    goto while_3_break;
  }
  while_3_break: ;
  }
  {
  while (1) {
    while_4_continue: ;
    {
    __cil_tmp16 = (unsigned int )head;
    __cil_tmp17 = *((struct list_head * const *)head);
    __cil_tmp18 = (unsigned int )__cil_tmp17;
    __cil_tmp19 = __cil_tmp18 != __cil_tmp16;
    if (! __cil_tmp19) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_4_break;
  }
  while_4_break: ;
  }
  {
  while (1) {
    while_5_continue: ;
    {
    __cil_tmp20 = (unsigned int )head;
    __cil_tmp21 = (unsigned int )head;
    __cil_tmp22 = __cil_tmp21 + 4;
    __cil_tmp23 = *((struct list_head * const *)__cil_tmp22);
    __cil_tmp24 = (unsigned int )__cil_tmp23;
    __cil_tmp25 = __cil_tmp24 != __cil_tmp20;
    if (! __cil_tmp25) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_5_break;
  }
  while_5_break: ;
  }
  __cil_tmp26 = (struct node *)0;
  __cil_tmp27 = (unsigned int )__cil_tmp26;
  __cil_tmp28 = __cil_tmp27 + 4;
  __cil_tmp29 = (struct list_head *)__cil_tmp28;
  __cil_tmp30 = (unsigned long )__cil_tmp29;
  __cil_tmp31 = (char *)head;
  __cil_tmp32 = __cil_tmp31 - __cil_tmp30;
  __cil_tmp33 = (struct node *)__cil_tmp32;
  node = (struct node const *)__cil_tmp33;
  {
  while (1) {
    while_6_continue: ;
    if (! node) {
      {
      fail();
      }
    } else {
    }
    goto while_6_break;
  }
  while_6_break: ;
  }
  {
  while (1) {
    while_7_continue: ;
    {
    __cil_tmp34 = (unsigned int )node;
    __cil_tmp35 = __cil_tmp34 + 12;
    __cil_tmp36 = (struct list_head const *)__cil_tmp35;
    __cil_tmp37 = (unsigned int )__cil_tmp36;
    __cil_tmp38 = (unsigned int )node;
    __cil_tmp39 = __cil_tmp38 + 12;
    __cil_tmp40 = *((struct list_head * const *)__cil_tmp39);
    __cil_tmp41 = (unsigned int )__cil_tmp40;
    __cil_tmp42 = __cil_tmp41 == __cil_tmp37;
    if (! __cil_tmp42) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_7_break;
  }
  while_7_break: ;
  }
  {
  while (1) {
    while_8_continue: ;
    {
    __cil_tmp43 = (unsigned int )node;
    __cil_tmp44 = __cil_tmp43 + 12;
    __cil_tmp45 = (struct list_head const *)__cil_tmp44;
    __cil_tmp46 = (unsigned int )__cil_tmp45;
    __cil_tmp47 = 12 + 4;
    __cil_tmp48 = (unsigned int )node;
    __cil_tmp49 = __cil_tmp48 + __cil_tmp47;
    __cil_tmp50 = *((struct list_head * const *)__cil_tmp49);
    __cil_tmp51 = (unsigned int )__cil_tmp50;
    __cil_tmp52 = __cil_tmp51 == __cil_tmp46;
    if (! __cil_tmp52) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_8_break;
  }
  while_8_break: ;
  }
  {
  while (1) {
    while_9_continue: ;
    {
    __cil_tmp53 = (unsigned int )node;
    __cil_tmp54 = __cil_tmp53 + 4;
    __cil_tmp55 = (struct list_head const *)__cil_tmp54;
    __cil_tmp56 = (unsigned int )__cil_tmp55;
    __cil_tmp57 = (unsigned int )node;
    __cil_tmp58 = __cil_tmp57 + 12;
    __cil_tmp59 = *((struct list_head * const *)__cil_tmp58);
    __cil_tmp60 = (unsigned int )__cil_tmp59;
    __cil_tmp61 = __cil_tmp60 != __cil_tmp56;
    if (! __cil_tmp61) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_9_break;
  }
  while_9_break: ;
  }
  {
  while (1) {
    while_10_continue: ;
    {
    __cil_tmp62 = (unsigned int )node;
    __cil_tmp63 = __cil_tmp62 + 4;
    __cil_tmp64 = (struct list_head const *)__cil_tmp63;
    __cil_tmp65 = (unsigned int )__cil_tmp64;
    __cil_tmp66 = 12 + 4;
    __cil_tmp67 = (unsigned int )node;
    __cil_tmp68 = __cil_tmp67 + __cil_tmp66;
    __cil_tmp69 = *((struct list_head * const *)__cil_tmp68);
    __cil_tmp70 = (unsigned int )__cil_tmp69;
    __cil_tmp71 = __cil_tmp70 != __cil_tmp65;
    if (! __cil_tmp71) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_10_break;
  }
  while_10_break: ;
  }
  {
  while (1) {
    while_11_continue: ;
    {
    __cil_tmp72 = (struct node const *)head;
    __cil_tmp73 = (unsigned int )__cil_tmp72;
    __cil_tmp74 = (unsigned int )node;
    __cil_tmp75 = __cil_tmp74 != __cil_tmp73;
    if (! __cil_tmp75) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_11_break;
  }
  while_11_break: ;
  }
  {
  while (1) {
    while_12_continue: ;
    {
    __cil_tmp76 = (unsigned int )node;
    __cil_tmp77 = __cil_tmp76 + 4;
    __cil_tmp78 = (struct list_head const *)__cil_tmp77;
    __cil_tmp79 = (struct node const *)__cil_tmp78;
    __cil_tmp80 = (unsigned int )__cil_tmp79;
    __cil_tmp81 = (unsigned int )node;
    __cil_tmp82 = __cil_tmp81 != __cil_tmp80;
    if (! __cil_tmp82) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_12_break;
  }
  while_12_break: ;
  }
  {
  while (1) {
    while_13_continue: ;
    {
    __cil_tmp83 = (int const *)node;
    __cil_tmp84 = (struct node const *)__cil_tmp83;
    __cil_tmp85 = (unsigned int )__cil_tmp84;
    __cil_tmp86 = (unsigned int )node;
    __cil_tmp87 = __cil_tmp86 == __cil_tmp85;
    if (! __cil_tmp87) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_13_break;
  }
  while_13_break: ;
  }
  {
  while (1) {
    while_14_continue: ;
    {
    __cil_tmp88 = (unsigned int )node;
    __cil_tmp89 = __cil_tmp88 + 4;
    __cil_tmp90 = *((struct list_head * const *)__cil_tmp89);
    __cil_tmp91 = (unsigned int )__cil_tmp90;
    __cil_tmp92 = __cil_tmp91 + 4;
    __cil_tmp93 = *((struct list_head **)__cil_tmp92);
    __cil_tmp94 = (unsigned int )__cil_tmp93;
    __cil_tmp95 = (unsigned int )head;
    __cil_tmp96 = __cil_tmp95 == __cil_tmp94;
    if (! __cil_tmp96) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_14_break;
  }
  while_14_break: ;
  }
  {
  while (1) {
    while_15_continue: ;
    {
    __cil_tmp97 = 4 + 4;
    __cil_tmp98 = (unsigned int )node;
    __cil_tmp99 = __cil_tmp98 + __cil_tmp97;
    __cil_tmp100 = *((struct list_head * const *)__cil_tmp99);
    __cil_tmp101 = *((struct list_head **)__cil_tmp100);
    __cil_tmp102 = (unsigned int )__cil_tmp101;
    __cil_tmp103 = (unsigned int )head;
    __cil_tmp104 = __cil_tmp103 == __cil_tmp102;
    if (! __cil_tmp104) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_15_break;
  }
  while_15_break: ;
  }
  __cil_tmp105 = *((struct list_head * const *)head);
  head = (struct list_head const *)__cil_tmp105;
  {
  while (1) {
    while_16_continue: ;
    {
    __cil_tmp106 = (unsigned int )head;
    __cil_tmp107 = (unsigned int )node;
    __cil_tmp108 = __cil_tmp107 + 4;
    __cil_tmp109 = (struct list_head const *)__cil_tmp108;
    __cil_tmp110 = (unsigned int )__cil_tmp109;
    if (__cil_tmp110 != __cil_tmp106) {
    } else {
      goto while_16_break;
    }
    }
    __cil_tmp111 = *((struct list_head * const *)head);
    head = (struct list_head const *)__cil_tmp111;
  }
  while_16_break: ;
  }
  {
  while (1) {
    while_17_continue: ;
    {
    __cil_tmp112 = (unsigned int )node;
    __cil_tmp113 = (struct node *)0;
    __cil_tmp114 = (unsigned int )__cil_tmp113;
    __cil_tmp115 = __cil_tmp114 + 4;
    __cil_tmp116 = (struct list_head *)__cil_tmp115;
    __cil_tmp117 = (unsigned long )__cil_tmp116;
    __cil_tmp118 = (char *)head;
    __cil_tmp119 = __cil_tmp118 - __cil_tmp117;
    __cil_tmp120 = (struct node *)__cil_tmp119;
    __cil_tmp121 = (unsigned int )__cil_tmp120;
    __cil_tmp122 = __cil_tmp121 == __cil_tmp112;
    if (! __cil_tmp122) {
      {
      fail();
      }
    } else {
    }
    }
    goto while_17_break;
  }
  while_17_break: ;
  }
  return;
}
}
__inline static void __list_add(struct list_head *new , struct list_head *prev , struct list_head *next )
{ unsigned int __cil_tmp4 ;
  unsigned int __cil_tmp5 ;
  unsigned int __cil_tmp6 ;
  unsigned int __cil_tmp7 ;
  {
  __cil_tmp4 = (unsigned int )next;
  __cil_tmp5 = __cil_tmp4 + 4;
  *((struct list_head **)__cil_tmp5) = new;
  *((struct list_head **)new) = next;
  __cil_tmp6 = (unsigned int )new;
  __cil_tmp7 = __cil_tmp6 + 4;
  *((struct list_head **)__cil_tmp7) = prev;
  *((struct list_head **)prev) = new;
  return;
}
}
__inline static void __list_del(struct list_head *prev , struct list_head *next )
{ unsigned int __cil_tmp3 ;
  unsigned int __cil_tmp4 ;
  {
  __cil_tmp3 = (unsigned int )next;
  __cil_tmp4 = __cil_tmp3 + 4;
  *((struct list_head **)__cil_tmp4) = prev;
  *((struct list_head **)prev) = next;
  return;
}
}
__inline static void list_add(struct list_head *new , struct list_head *head )
{ struct list_head *__cil_tmp3 ;
  {
  {
  __cil_tmp3 = *((struct list_head **)head);
  __list_add(new, head, __cil_tmp3);
  }
  return;
}
}
__inline static void list_move(struct list_head *list , struct list_head *head )
{ unsigned int __cil_tmp3 ;
  unsigned int __cil_tmp4 ;
  struct list_head *__cil_tmp5 ;
  struct list_head *__cil_tmp6 ;
  {
  {
  __cil_tmp3 = (unsigned int )list;
  __cil_tmp4 = __cil_tmp3 + 4;
  __cil_tmp5 = *((struct list_head **)__cil_tmp4);
  __cil_tmp6 = *((struct list_head **)list);
  __list_del(__cil_tmp5, __cil_tmp6);
  list_add(list, head);
  }
  return;
}
}
static void gl_insert(int value )
{ struct node *node ;
  void *tmp ;
  unsigned int __cil_tmp4 ;
  unsigned int __cil_tmp5 ;
  unsigned int __cil_tmp6 ;
  struct list_head *__cil_tmp7 ;
  unsigned int __cil_tmp8 ;
  unsigned int __cil_tmp9 ;
  unsigned int __cil_tmp10 ;
  unsigned int __cil_tmp11 ;
  unsigned int __cil_tmp12 ;
  unsigned int __cil_tmp13 ;
  unsigned int __cil_tmp14 ;
  unsigned int __cil_tmp15 ;
  {
  {
  __cil_tmp4 = (unsigned int )20UL;
  tmp = malloc(__cil_tmp4);
  node = (struct node *)tmp;
  }
  if (! node) {
    {
    abort();
    }
  } else {
  }
  {
  *((int *)node) = value;
  __cil_tmp5 = (unsigned int )node;
  __cil_tmp6 = __cil_tmp5 + 4;
  __cil_tmp7 = (struct list_head *)__cil_tmp6;
  list_add(__cil_tmp7, & gl_list);
  }
  {
  while (1) {
    while_18_continue: ;
    __cil_tmp8 = (unsigned int )node;
    __cil_tmp9 = __cil_tmp8 + 12;
    __cil_tmp10 = (unsigned int )node;
    __cil_tmp11 = __cil_tmp10 + 12;
    *((struct list_head **)__cil_tmp9) = (struct list_head *)__cil_tmp11;
    __cil_tmp12 = (unsigned int )node;
    __cil_tmp13 = __cil_tmp12 + 12;
    __cil_tmp14 = (unsigned int )node;
    __cil_tmp15 = __cil_tmp14 + 12;
    *((struct list_head **)__cil_tmp13) = (struct list_head *)__cil_tmp15;
    goto while_18_break;
  }
  while_18_break: ;
  }
  return;
}
}
static void gl_read(void)
{ int tmp ;
  int tmp___0 ;
  {
  {
  while (1) {
    while_19_continue: ;
    {
    tmp = __VERIFIER_nondet_int();
    gl_insert(tmp);
    tmp___0 = __VERIFIER_nondet_int();
    }
    if (tmp___0) {
    } else {
      goto while_19_break;
    }
  }
  while_19_break: ;
  }
  return;
}
}
static void gl_destroy(void)
{ struct list_head *next ;
  struct list_head *__cil_tmp2 ;
  unsigned int __cil_tmp3 ;
  unsigned int __cil_tmp4 ;
  struct list_head *__cil_tmp5 ;
  struct node *__cil_tmp6 ;
  unsigned int __cil_tmp7 ;
  unsigned int __cil_tmp8 ;
  struct list_head *__cil_tmp9 ;
  unsigned long __cil_tmp10 ;
  char *__cil_tmp11 ;
  char *__cil_tmp12 ;
  struct node *__cil_tmp13 ;
  void *__cil_tmp14 ;
  {
  {
  while (1) {
    while_20_continue: ;
    __cil_tmp2 = & gl_list;
    next = *((struct list_head **)__cil_tmp2);
    {
    __cil_tmp3 = (unsigned int )next;
    __cil_tmp4 = (unsigned int )(& gl_list);
    if (__cil_tmp4 != __cil_tmp3) {
    } else {
      goto while_20_break;
    }
    }
    {
    __cil_tmp5 = & gl_list;
    *((struct list_head **)__cil_tmp5) = *((struct list_head **)next);
    __cil_tmp6 = (struct node *)0;
    __cil_tmp7 = (unsigned int )__cil_tmp6;
    __cil_tmp8 = __cil_tmp7 + 4;
    __cil_tmp9 = (struct list_head *)__cil_tmp8;
    __cil_tmp10 = (unsigned long )__cil_tmp9;
    __cil_tmp11 = (char *)next;
    __cil_tmp12 = __cil_tmp11 - __cil_tmp10;
    __cil_tmp13 = (struct node *)__cil_tmp12;
    __cil_tmp14 = (void *)__cil_tmp13;
    free(__cil_tmp14);
    }
  }
  while_20_break: ;
  }
  return;
}
}
static int val_from_node(struct list_head *head )
{ struct node *entry ;
  struct node *__cil_tmp3 ;
  unsigned int __cil_tmp4 ;
  unsigned int __cil_tmp5 ;
  struct list_head *__cil_tmp6 ;
  unsigned long __cil_tmp7 ;
  char *__cil_tmp8 ;
  char *__cil_tmp9 ;
  {
  __cil_tmp3 = (struct node *)0;
  __cil_tmp4 = (unsigned int )__cil_tmp3;
  __cil_tmp5 = __cil_tmp4 + 4;
  __cil_tmp6 = (struct list_head *)__cil_tmp5;
  __cil_tmp7 = (unsigned long )__cil_tmp6;
  __cil_tmp8 = (char *)head;
  __cil_tmp9 = __cil_tmp8 - __cil_tmp7;
  entry = (struct node *)__cil_tmp9;
  return (*((int *)entry));
}
}
static _Bool gl_sort_pass(void)
{ _Bool any_change ;
  struct list_head *pos0 ;
  struct list_head *pos1 ;
  int val0 ;
  int tmp ;
  int val1 ;
  int tmp___0 ;
  struct list_head *__cil_tmp8 ;
  unsigned int __cil_tmp9 ;
  unsigned int __cil_tmp10 ;
  {
  any_change = (_Bool)0;
  __cil_tmp8 = & gl_list;
  pos0 = *((struct list_head **)__cil_tmp8);
  {
  while (1) {
    while_21_continue: ;
    pos1 = *((struct list_head **)pos0);
    {
    __cil_tmp9 = (unsigned int )pos1;
    __cil_tmp10 = (unsigned int )(& gl_list);
    if (__cil_tmp10 != __cil_tmp9) {
    } else {
      goto while_21_break;
    }
    }
    {
    tmp = val_from_node(pos0);
    val0 = tmp;
    tmp___0 = val_from_node(pos1);
    val1 = tmp___0;
    }
    if (val0 <= val1) {
      pos0 = pos1;
      goto while_21_continue;
    } else {
    }
    {
    any_change = (_Bool)1;
    list_move(pos0, pos1);
    }
  }
  while_21_break: ;
  }
  return (any_change);
}
}
static void gl_sort(void)
{ _Bool tmp ;
  {
  {
  while (1) {
    while_22_continue: ;
    {
    tmp = gl_sort_pass();
    }
    if (tmp) {
    } else {
      goto while_22_break;
    }
  }
  while_22_break: ;
  }
  return;
}
}
int main(void)
{ struct list_head const *__cil_tmp1 ;
  struct list_head const *__cil_tmp2 ;
  {
  {
  gl_read();
  __cil_tmp1 = (struct list_head const *)(& gl_list);
  inspect(__cil_tmp1);
  gl_sort();
  __cil_tmp2 = (struct list_head const *)(& gl_list);
  inspect(__cil_tmp2);
  gl_destroy();
  }
  return (0);
}
}
