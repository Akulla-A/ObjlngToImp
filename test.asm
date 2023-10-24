.text
	beqz $a0, init_end
	lw $a0, 0($a1)
	jal atoi
init_end:
	subi $sp, $sp, 4
	sw $v0, 0($sp)
	jal main
	li $v0, 10
	syscall
point3D_getValues:
	subi $sp, $sp, 4
	sw $fp, 0($sp)
	subi $sp, $sp, 4
	sw $ra, 0($sp)
	addi $fp, $sp, 4
	addi $sp, $sp, 0
	li $t0, 16
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	li $t0, 8
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	li $t0, 4
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	addi $sp, $fp, -4
	lw $ra, 0($sp)
	addi $sp, $sp, 4
	lw $fp, 0($sp)
	addi $sp, $sp, 4
	jr $ra
	li $t0, 0
	addi $sp, $fp, -4
	lw $ra, 0($sp)
	addi $sp, $sp, 4
	lw $fp, 0($sp)
	addi $sp, $sp, 4
	jr $ra
point3D_sum:
	subi $sp, $sp, 4
	sw $fp, 0($sp)
	subi $sp, $sp, 4
	sw $ra, 0($sp)
	addi $fp, $sp, 4
	addi $sp, $sp, 0
	li $t0, 16
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	li $t0, 8
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	li $t0, 4
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 8($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	addi $sp, $fp, -4
	lw $ra, 0($sp)
	addi $sp, $sp, 4
	lw $fp, 0($sp)
	addi $sp, $sp, 4
	jr $ra
	li $t0, 0
	addi $sp, $fp, -4
	lw $ra, 0($sp)
	addi $sp, $sp, 4
	lw $fp, 0($sp)
	addi $sp, $sp, 4
	jr $ra
point3D_constructor:
	subi $sp, $sp, 4
	sw $fp, 0($sp)
	subi $sp, $sp, 4
	sw $ra, 0($sp)
	addi $fp, $sp, 4
	addi $sp, $sp, 0
	li $t0, 4
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 8($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 8
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 12($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 16
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 16($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 0
	addi $sp, $fp, -4
	lw $ra, 0($sp)
	addi $sp, $sp, 4
	lw $fp, 0($sp)
	addi $sp, $sp, 4
	jr $ra
point_sum:
	subi $sp, $sp, 4
	sw $fp, 0($sp)
	subi $sp, $sp, 4
	sw $ra, 0($sp)
	addi $fp, $sp, 4
	addi $sp, $sp, 0
	li $t0, 8
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	li $t0, 4
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 8($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	addi $sp, $fp, -4
	lw $ra, 0($sp)
	addi $sp, $sp, 4
	lw $fp, 0($sp)
	addi $sp, $sp, 4
	jr $ra
	li $t0, 0
	addi $sp, $fp, -4
	lw $ra, 0($sp)
	addi $sp, $sp, 4
	lw $fp, 0($sp)
	addi $sp, $sp, 4
	jr $ra
point_constructor:
	subi $sp, $sp, 4
	sw $fp, 0($sp)
	subi $sp, $sp, 4
	sw $ra, 0($sp)
	addi $fp, $sp, 4
	addi $sp, $sp, 0
	li $t0, 4
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 8($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 8
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 4($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, 12($fp)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 0
	addi $sp, $fp, -4
	lw $ra, 0($sp)
	addi $sp, $sp, 4
	lw $fp, 0($sp)
	addi $sp, $sp, 4
	jr $ra
main:
	subi $sp, $sp, 4
	sw $fp, 0($sp)
	subi $sp, $sp, 4
	sw $ra, 0($sp)
	addi $fp, $sp, 4
	addi $sp, $sp, -12
	li $t0, 16
	move $a0, $t0
	li $v0, 9
	syscall
	move $t0, $v0
	la $t1, point3D_descr
	sw $t0, 0($t1)
	li $t0, 0
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point3D_descr
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point_descr
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 12
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point3D_descr
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point3D_constructor
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 8
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point3D_descr
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point3D_getValues
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 4
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point3D_descr
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point3D_sum
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 12
	move $a0, $t0
	li $v0, 9
	syscall
	move $t0, $v0
	la $t1, point_descr
	sw $t0, 0($t1)
	li $t0, 0
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point_descr
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	li $t0, 0
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 8
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point_descr
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point_constructor
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 4
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point_descr
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point_sum
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 16
	move $a0, $t0
	li $v0, 9
	syscall
	move $t0, $v0
	sw $t0, -8($fp)
	lw $t0, -8($fp)
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point3D_descr
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 0
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	li $t0, 1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	li $t0, 2
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, -8($fp)
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	li $t0, 12
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point3D_descr
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	jalr $t0
	addi $sp, $sp, 16
	li $t0, 48
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, -8($fp)
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	li $t0, 4
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, -8($fp)
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	jalr $t0
	addi $sp, $sp, 8
	sw $t0, -12($fp)
	li $t0, 12
	move $a0, $t0
	li $v0, 9
	syscall
	move $t0, $v0
	sw $t0, -16($fp)
	lw $t0, -16($fp)
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point_descr
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	sw $t0, 0($t1)
	li $t0, 1
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	li $t0, 2
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	lw $t0, -16($fp)
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	li $t0, 8
	subi $sp, $sp, 4
	sw $t0, 0($sp)
	la $t0, point_descr
	lw $t0, 0($t0)
	lw $t1, 0($sp)
	addi $sp, $sp, 4
	add $t0, $t0, $t1
	lw $t0, 0($t0)
	jalr $t0
	addi $sp, $sp, 12
	lw $t0, -12($fp)
	move $a0, $t0
	li $v0, 11
	syscall
	li $t0, 0
	addi $sp, $fp, -4
	lw $ra, 0($sp)
	addi $sp, $sp, 4
	lw $fp, 0($sp)
	addi $sp, $sp, 4
	jr $ra
#built-in atoi
atoi:
	li $v0, 0
atoi_loop:
	lbu $t0, 0($a0)
	beqz $t0, atoi_end
	addi $t0, $t0, -48
	bltz $t0, atoi_error
	bge $t0, 10, atoi_error
	mul $v0, $v0, 10
	add $v0, $v0, $t0
	addi $a0, $a0, 1
	b atoi_loop
atoi_error:
	li $v0, 10
	syscall
atoi_end:
	jr $ra
.data
_instanceof_ptr:
	.word 0
point3D_descr:
	.word 0
point_descr:
	.word 0
